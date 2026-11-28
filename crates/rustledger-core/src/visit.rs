//! Visitors for AST positions that carry a currency or an account name.
//!
//! These exist because hand-rolled "for each currency / for each
//! account" walks across the AST kept missing positions. The earlier
//! pattern was: every consumer (LSP completion, hover usage count,
//! WASM editor extraction, etc.) wrote its own walk over `Directive`
//! variants, and silently dropped any position the author happened
//! not to remember (`Note.account`, `Posting.cost.currency`,
//! `MetaValue::Account` metadata values, `Custom.values`, …).
//! Fixing it in five different files left the underlying problem
//! intact: the next contributor writing a "for each X" walk will
//! reach for the same shape and reintroduce the same bug class.
//!
//! These visitors are the canonical answer. Every position that
//! carries a currency or an account name is enumerated exactly once
//! here, with no `_ => {}` catch-all — at any layer of the match.
//! That means:
//!
//! - A future `Directive` variant added to the enum forces a
//!   compile error at the top-level `visit_*` match.
//! - A future `MetaValue` variant forces a compile error at
//!   `visit_meta_value_currency` and `visit_meta_value_account`.
//! - A future `PriceAnnotation` variant forces a compile error at
//!   `visit_price_currency`.
//!
//! This file is the ONE place that needs to be updated when new
//! variants are added to any of those enums. Downstream consumers
//! calling `visit_*` benefit automatically.
//!
//! Spans of source tokens are intentionally NOT exposed here:
//! source positions are parser-only metadata published via
//! `ParseResult::currency_occurrences` (the parser is the canonical
//! owner of source-position data). Value-level consumers (extract,
//! hover usage count, completion suggestions) want the strings;
//! source-position consumers (LSP rename / references /
//! document-highlight / linked-editing / goto-definition) consume
//! the parser's index. Separating the concerns keeps the AST
//! value types pure.

use crate::{
    CostNumber, Decimal, Directive, IncompleteAmount, MetaValue, Metadata, PriceAnnotation,
};

/// Walk every position a currency name can appear in this directive,
/// invoking `visit` once per occurrence.
///
/// Positions covered:
/// - `Open.currencies` (each constraint entry)
/// - `Commodity.currency` (the declared currency)
/// - `Balance.amount.currency`
/// - `Price` directive (base `currency` and `amount.currency`)
/// - `Posting.units.currency()` (units side, including `CurrencyOnly`)
/// - `Posting.cost.currency` (cost spec)
/// - `Posting.price` (any `PriceAnnotation`, regardless of `kind`)
/// - `MetaValue::Currency` / `MetaValue::Amount` in any directive's
///   or posting's metadata block
/// - `Custom.values` entries that are `MetaValue::Currency` or
///   `MetaValue::Amount`
///
/// The visit order within a directive is the order tokens appear in
/// source for the parser-generated AST; metadata is visited in its
/// insertion order, which for a parsed directive is source order.
pub fn visit_currencies<'a>(directive: &'a Directive, visit: &mut impl FnMut(&'a str)) {
    match directive {
        Directive::Open(open) => {
            for currency in &open.currencies {
                visit(currency.as_str());
            }
            visit_meta_currencies(&open.meta, visit);
        }
        Directive::Commodity(comm) => {
            visit(comm.currency.as_str());
            visit_meta_currencies(&comm.meta, visit);
        }
        Directive::Balance(bal) => {
            visit(bal.amount.currency.as_str());
            visit_meta_currencies(&bal.meta, visit);
        }
        Directive::Price(price) => {
            visit(price.currency.as_str());
            visit(price.amount.currency.as_str());
            visit_meta_currencies(&price.meta, visit);
        }
        Directive::Transaction(txn) => {
            visit_meta_currencies(&txn.meta, visit);
            for posting in &txn.postings {
                if let Some(units) = &posting.units
                    && let Some(c) = units.currency()
                {
                    visit(c);
                }
                if let Some(cost) = &posting.cost
                    && let Some(c) = &cost.currency
                {
                    visit(c.as_str());
                }
                if let Some(price) = &posting.price {
                    visit_price_currency(price, visit);
                }
                visit_meta_currencies(&posting.meta, visit);
            }
        }
        Directive::Custom(custom) => {
            for v in &custom.values {
                visit_meta_value_currency(v, visit);
            }
            visit_meta_currencies(&custom.meta, visit);
        }
        Directive::Note(note) => visit_meta_currencies(&note.meta, visit),
        Directive::Document(doc) => visit_meta_currencies(&doc.meta, visit),
        Directive::Close(close) => visit_meta_currencies(&close.meta, visit),
        Directive::Pad(pad) => visit_meta_currencies(&pad.meta, visit),
        Directive::Event(event) => visit_meta_currencies(&event.meta, visit),
        Directive::Query(query) => visit_meta_currencies(&query.meta, visit),
    }
}

/// Walk every position an account name can appear in this directive,
/// invoking `visit` once per occurrence.
///
/// Positions covered:
/// - `Open.account`, `Close.account`
/// - `Balance.account`
/// - `Pad.account`, `Pad.source_account`
/// - `Note.account`, `Document.account`
/// - `Posting.account` (transactions)
/// - `MetaValue::Account` in any directive's or posting's metadata
/// - `Custom.values` entries that are `MetaValue::Account`
///
/// Visit order matches the source order of the parser-generated
/// AST; metadata is visited in its insertion (source) order.
pub fn visit_accounts<'a>(directive: &'a Directive, visit: &mut impl FnMut(&'a str)) {
    match directive {
        Directive::Open(open) => {
            visit(open.account.as_str());
            visit_meta_accounts(&open.meta, visit);
        }
        Directive::Close(close) => {
            visit(close.account.as_str());
            visit_meta_accounts(&close.meta, visit);
        }
        Directive::Balance(bal) => {
            visit(bal.account.as_str());
            visit_meta_accounts(&bal.meta, visit);
        }
        Directive::Pad(pad) => {
            visit(pad.account.as_str());
            visit(pad.source_account.as_str());
            visit_meta_accounts(&pad.meta, visit);
        }
        Directive::Note(note) => {
            visit(note.account.as_str());
            visit_meta_accounts(&note.meta, visit);
        }
        Directive::Document(doc) => {
            visit(doc.account.as_str());
            visit_meta_accounts(&doc.meta, visit);
        }
        Directive::Transaction(txn) => {
            visit_meta_accounts(&txn.meta, visit);
            for posting in &txn.postings {
                visit(posting.account.as_str());
                visit_meta_accounts(&posting.meta, visit);
            }
        }
        Directive::Custom(custom) => {
            for v in &custom.values {
                visit_meta_value_account(v, visit);
            }
            visit_meta_accounts(&custom.meta, visit);
        }
        Directive::Commodity(comm) => visit_meta_accounts(&comm.meta, visit),
        Directive::Price(price) => visit_meta_accounts(&price.meta, visit),
        Directive::Event(event) => visit_meta_accounts(&event.meta, visit),
        Directive::Query(query) => visit_meta_accounts(&query.meta, visit),
    }
}

/// Walk every position a tag can appear in this directive, invoking
/// `visit` once per occurrence (tag text without the `#` sigil).
///
/// Positions covered:
/// - `Transaction.tags` (including tags folded in from `pushtag`)
/// - `Document.tags`
/// - `Note.tags` (since #2160; before that a note's tags never reached the
///   model, so this list was complete without it)
/// - `MetaValue::Tag` in any directive's or posting's metadata. Reachable
///   from source: `mytag: #foo` parses, matching beancount, which accepts a
///   tag as a metadata value (and stores it as a bare string). A key of one
///   character is rejected whatever follows it, so `t: #foo` fails on the
///   KEY -- which once led to this branch being reported as dead (#2190).
/// - `Custom.values` entries that are `MetaValue::Tag`. NOT reachable from
///   source: a tag is not a valid custom value in either tool, and since
///   #2190 the parser no longer emits the value it rejected. Kept because a
///   plugin can supply one -- `from_wrapper` maps `MetaValueData::Tag` onto
///   this variant -- so the arm collects plugin output, not parser output.
///
/// Visit order matches the source order of the parser-generated AST;
/// metadata is visited in its insertion (source) order.
pub fn visit_tags<'a>(directive: &'a Directive, visit: &mut impl FnMut(&'a str)) {
    match directive {
        Directive::Transaction(txn) => {
            for tag in &txn.tags {
                visit(tag.as_str());
            }
            visit_meta_tags(&txn.meta, visit);
            for posting in &txn.postings {
                visit_meta_tags(&posting.meta, visit);
            }
        }
        Directive::Document(doc) => {
            for tag in &doc.tags {
                visit(tag.as_str());
            }
            visit_meta_tags(&doc.meta, visit);
        }
        Directive::Custom(custom) => {
            for v in &custom.values {
                visit_meta_value_tag(v, visit);
            }
            visit_meta_tags(&custom.meta, visit);
        }
        Directive::Open(open) => visit_meta_tags(&open.meta, visit),
        Directive::Close(close) => visit_meta_tags(&close.meta, visit),
        Directive::Commodity(comm) => visit_meta_tags(&comm.meta, visit),
        Directive::Balance(bal) => visit_meta_tags(&bal.meta, visit),
        Directive::Pad(pad) => visit_meta_tags(&pad.meta, visit),
        Directive::Note(note) => {
            for tag in &note.tags {
                visit(tag.as_str());
            }
            visit_meta_tags(&note.meta, visit);
        }
        Directive::Price(price) => visit_meta_tags(&price.meta, visit),
        Directive::Event(event) => visit_meta_tags(&event.meta, visit),
        Directive::Query(query) => visit_meta_tags(&query.meta, visit),
    }
}

/// Walk every position a link can appear in this directive, invoking
/// `visit` once per occurrence (link text without the `^` sigil).
///
/// Positions covered mirror [`visit_tags`], with `Link` in place of
/// `Tag`: `Transaction.links`, `Document.links`, `Note.links` (since
/// #2160), `MetaValue::Link` in metadata, and `Custom.values` link entries.
///
/// The last two differ from their tag counterparts in where they can come
/// from. A `^link` is NOT a valid metadata value in either tool, and is not a
/// valid custom value either, so neither reaches this function from parsed
/// source. Both remain live because `from_wrapper` maps
/// `MetaValueData::Link` onto `MetaValue::Link`: a plugin can put a link in
/// metadata, and this is what collects it (#2190).
pub fn visit_links<'a>(directive: &'a Directive, visit: &mut impl FnMut(&'a str)) {
    match directive {
        Directive::Transaction(txn) => {
            for link in &txn.links {
                visit(link.as_str());
            }
            visit_meta_links(&txn.meta, visit);
            for posting in &txn.postings {
                visit_meta_links(&posting.meta, visit);
            }
        }
        Directive::Document(doc) => {
            for link in &doc.links {
                visit(link.as_str());
            }
            visit_meta_links(&doc.meta, visit);
        }
        Directive::Custom(custom) => {
            for v in &custom.values {
                visit_meta_value_link(v, visit);
            }
            visit_meta_links(&custom.meta, visit);
        }
        Directive::Open(open) => visit_meta_links(&open.meta, visit),
        Directive::Close(close) => visit_meta_links(&close.meta, visit),
        Directive::Commodity(comm) => visit_meta_links(&comm.meta, visit),
        Directive::Balance(bal) => visit_meta_links(&bal.meta, visit),
        Directive::Pad(pad) => visit_meta_links(&pad.meta, visit),
        Directive::Note(note) => {
            for link in &note.links {
                visit(link.as_str());
            }
            visit_meta_links(&note.meta, visit);
        }
        Directive::Price(price) => visit_meta_links(&price.meta, visit),
        Directive::Event(event) => visit_meta_links(&event.meta, visit),
        Directive::Query(query) => visit_meta_links(&query.meta, visit),
    }
}

fn visit_meta_currencies<'a>(meta: &'a Metadata, visit: &mut impl FnMut(&'a str)) {
    for v in meta.values() {
        visit_meta_value_currency(v, visit);
    }
}

fn visit_meta_tags<'a>(meta: &'a Metadata, visit: &mut impl FnMut(&'a str)) {
    for v in meta.values() {
        visit_meta_value_tag(v, visit);
    }
}

fn visit_meta_links<'a>(meta: &'a Metadata, visit: &mut impl FnMut(&'a str)) {
    for v in meta.values() {
        visit_meta_value_link(v, visit);
    }
}

fn visit_meta_accounts<'a>(meta: &'a Metadata, visit: &mut impl FnMut(&'a str)) {
    for v in meta.values() {
        visit_meta_value_account(v, visit);
    }
}

/// Per-`MetaValue` currency extractor. Used both by metadata-block
/// walks and by `Custom.values` walks (Custom directives carry a
/// `Vec<MetaValue>` as positional args; the same per-variant logic
/// applies). The match is exhaustive with no `_ => {}` catch-all —
/// a future `MetaValue` variant added to the enum forces a compile
/// error here and at `visit_meta_value_account`, so the visitor
/// stays in lockstep with the type definition. Mirrors the no-
/// catch-all guarantee already enforced on the `Directive` match
/// at the top of this module.
fn visit_meta_value_currency<'a>(v: &'a MetaValue, visit: &mut impl FnMut(&'a str)) {
    match v {
        MetaValue::Currency(s) => visit(s.as_str()),
        MetaValue::Amount(a) => visit(a.currency.as_str()),
        // Variants that cannot carry a currency.
        MetaValue::String(_)
        | MetaValue::Account(_)
        | MetaValue::Tag(_)
        | MetaValue::Link(_)
        | MetaValue::Date(_)
        | MetaValue::Number(_)
        | MetaValue::Bool(_)
        | MetaValue::Int(_)
        | MetaValue::None => {}
    }
}

/// Per-`MetaValue` account extractor. See `visit_meta_value_currency`
/// for the no-`_ => {}`-catch-all rationale.
fn visit_meta_value_account<'a>(v: &'a MetaValue, visit: &mut impl FnMut(&'a str)) {
    match v {
        MetaValue::Account(a) => visit(a.as_str()),
        // Variants that cannot carry an account name.
        MetaValue::String(_)
        | MetaValue::Currency(_)
        | MetaValue::Tag(_)
        | MetaValue::Link(_)
        | MetaValue::Date(_)
        | MetaValue::Number(_)
        | MetaValue::Bool(_)
        | MetaValue::Amount(_)
        | MetaValue::Int(_)
        | MetaValue::None => {}
    }
}

/// Per-`MetaValue` tag extractor (tag text without the `#`). See
/// `visit_meta_value_currency` for the no-`_ => {}`-catch-all rationale.
fn visit_meta_value_tag<'a>(v: &'a MetaValue, visit: &mut impl FnMut(&'a str)) {
    match v {
        MetaValue::Tag(t) => visit(t.as_str()),
        // Variants that cannot carry a tag.
        MetaValue::String(_)
        | MetaValue::Account(_)
        | MetaValue::Currency(_)
        | MetaValue::Link(_)
        | MetaValue::Date(_)
        | MetaValue::Number(_)
        | MetaValue::Bool(_)
        | MetaValue::Amount(_)
        | MetaValue::Int(_)
        | MetaValue::None => {}
    }
}

/// Per-`MetaValue` link extractor (link text without the `^`). See
/// `visit_meta_value_currency` for the no-`_ => {}`-catch-all rationale.
fn visit_meta_value_link<'a>(v: &'a MetaValue, visit: &mut impl FnMut(&'a str)) {
    match v {
        MetaValue::Link(l) => visit(l.as_str()),
        // Variants that cannot carry a link.
        MetaValue::String(_)
        | MetaValue::Account(_)
        | MetaValue::Currency(_)
        | MetaValue::Tag(_)
        | MetaValue::Date(_)
        | MetaValue::Number(_)
        | MetaValue::Bool(_)
        | MetaValue::Amount(_)
        | MetaValue::Int(_)
        | MetaValue::None => {}
    }
}

fn visit_price_currency<'a>(price: &'a PriceAnnotation, visit: &mut impl FnMut(&'a str)) {
    // Post-#1167: PriceAnnotation factors into orthogonal kind+amount
    // axes, so the six pre-#1167 arms collapse to one inspection of
    // `amount`. The `kind` (Unit vs Total) is irrelevant for currency
    // extraction.
    match &price.amount {
        Some(IncompleteAmount::Complete(amt)) => visit(amt.currency.as_str()),
        Some(inc) => {
            if let Some(c) = inc.currency() {
                visit(c);
            }
        }
        None => {}
    }
}

/// Walk every decimal number in this directive, invoking `visit` once per
/// occurrence, in source order.
///
/// `Decimal`'s `PartialEq` ignores scale (`1.5 == 1.50`), but the scale is
/// meaning in beancount (display precision, tolerance inference), so a
/// comparison that must see it walks the numbers with this and compares
/// each one exactly (the formatter's certifier, which checks that
/// formatting kept what a file means).
///
/// Positions covered:
/// - `Posting.units` (`Complete` and `NumberOnly`)
/// - `Posting.cost.number` (every `CostNumber` shape)
/// - `Posting.price` amount
/// - `Balance.amount`, `Balance.tolerance`
/// - `Price.amount`
/// - `MetaValue::Number` / `MetaValue::Amount` in any directive's or
///   posting's metadata, in insertion order
/// - `Custom.values` entries that are `MetaValue::Number` or
///   `MetaValue::Amount`
pub fn visit_numbers<'a>(directive: &'a Directive, visit: &mut impl FnMut(&'a Decimal)) {
    match directive {
        Directive::Transaction(txn) => {
            visit_meta_numbers(&txn.meta, visit);
            for posting in &txn.postings {
                if let Some(units) = &posting.units {
                    visit_incomplete_amount_number(units, visit);
                }
                if let Some(cost) = &posting.cost
                    && let Some(number) = &cost.number
                {
                    match number {
                        CostNumber::PerUnit { value } | CostNumber::Total { value } => visit(value),
                        CostNumber::PerUnitFromTotal(booked) => {
                            visit(&booked.per_unit);
                            visit(&booked.total);
                        }
                        CostNumber::Compound { per_unit, total } => {
                            visit(per_unit);
                            visit(total);
                        }
                    }
                }
                if let Some(price) = &posting.price
                    && let Some(amount) = &price.amount
                {
                    visit_incomplete_amount_number(amount, visit);
                }
                visit_meta_numbers(&posting.meta, visit);
            }
        }
        Directive::Balance(bal) => {
            visit(&bal.amount.number);
            if let Some(tolerance) = &bal.tolerance {
                visit(tolerance);
            }
            visit_meta_numbers(&bal.meta, visit);
        }
        Directive::Price(price) => {
            visit(&price.amount.number);
            visit_meta_numbers(&price.meta, visit);
        }
        Directive::Custom(custom) => {
            for v in &custom.values {
                visit_meta_value_number(v, visit);
            }
            visit_meta_numbers(&custom.meta, visit);
        }
        Directive::Open(open) => visit_meta_numbers(&open.meta, visit),
        Directive::Close(close) => visit_meta_numbers(&close.meta, visit),
        Directive::Commodity(comm) => visit_meta_numbers(&comm.meta, visit),
        Directive::Pad(pad) => visit_meta_numbers(&pad.meta, visit),
        Directive::Event(event) => visit_meta_numbers(&event.meta, visit),
        Directive::Query(query) => visit_meta_numbers(&query.meta, visit),
        Directive::Note(note) => visit_meta_numbers(&note.meta, visit),
        Directive::Document(doc) => visit_meta_numbers(&doc.meta, visit),
    }
}

/// Walk every metadata block of this directive, invoking `visit` once per
/// block: the directive's own, then each posting's, in source order.
///
/// `Metadata`'s `PartialEq` is order-independent, while the order its keys
/// were written in reaches every printed form; a comparison that must see
/// the order walks the blocks with this.
pub fn visit_metadata<'a>(directive: &'a Directive, visit: &mut impl FnMut(&'a Metadata)) {
    visit(directive.meta());
    if let Directive::Transaction(txn) = directive {
        for posting in &txn.postings {
            visit(&posting.meta);
        }
    }
}

fn visit_incomplete_amount_number<'a>(
    amount: &'a IncompleteAmount,
    visit: &mut impl FnMut(&'a Decimal),
) {
    match amount {
        IncompleteAmount::Complete(a) => visit(&a.number),
        IncompleteAmount::NumberOnly(n) => visit(n),
        IncompleteAmount::CurrencyOnly(_) => {}
    }
}

fn visit_meta_numbers<'a>(meta: &'a Metadata, visit: &mut impl FnMut(&'a Decimal)) {
    for v in meta.values() {
        visit_meta_value_number(v, visit);
    }
}

/// Per-`MetaValue` number extractor. See `visit_meta_value_currency` for the
/// no-`_ => {}`-catch-all rationale.
fn visit_meta_value_number<'a>(v: &'a MetaValue, visit: &mut impl FnMut(&'a Decimal)) {
    match v {
        MetaValue::Number(n) => visit(n),
        MetaValue::Amount(a) => visit(&a.number),
        // Variants that carry no decimal (`Int` is an integer, which
        // `PartialEq` already compares exactly).
        MetaValue::String(_)
        | MetaValue::Account(_)
        | MetaValue::Currency(_)
        | MetaValue::Tag(_)
        | MetaValue::Link(_)
        | MetaValue::Date(_)
        | MetaValue::Bool(_)
        | MetaValue::Int(_)
        | MetaValue::None => {}
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{
        Amount, Balance, Close, Commodity, CostSpec, Custom, Document, MetaValue, Metadata,
        NaiveDate, Note, Open, Pad, Posting, Price, Spanned, Transaction,
    };
    use rust_decimal_macros::dec;

    fn date(y: i32, m: u32, d: u32) -> NaiveDate {
        crate::naive_date(y, m, d).unwrap()
    }

    fn collect_currencies(directives: &[Directive]) -> Vec<String> {
        let mut out = Vec::new();
        for d in directives {
            visit_currencies(d, &mut |c| out.push(c.to_string()));
        }
        out
    }

    fn collect_accounts(directives: &[Directive]) -> Vec<String> {
        let mut out = Vec::new();
        for d in directives {
            visit_accounts(d, &mut |a| out.push(a.to_string()));
        }
        out
    }

    fn collect_tags(directives: &[Directive]) -> Vec<String> {
        let mut out = Vec::new();
        for d in directives {
            visit_tags(d, &mut |t| out.push(t.to_string()));
        }
        out
    }

    fn collect_links(directives: &[Directive]) -> Vec<String> {
        let mut out = Vec::new();
        for d in directives {
            visit_links(d, &mut |l| out.push(l.to_string()));
        }
        out
    }

    /// `visit_currencies` must surface every Currency-bearing
    /// position. This test seeds USD into all 11 positions and
    /// asserts the visitor reaches each one.
    #[test]
    fn test_visit_currencies_reaches_every_position() {
        let mut commodity_meta: Metadata = Default::default();
        commodity_meta.insert("note", MetaValue::Currency("USD".into()));

        let mut txn_meta: Metadata = Default::default();
        txn_meta.insert("settled", MetaValue::Amount(Amount::new(dec!(1), "USD")));

        let directives = vec![
            // Open.currencies + meta
            Directive::Open(Open {
                date: date(2024, 1, 1),
                account: "Assets:Cash".into(),
                currencies: vec!["USD".into()],
                booking: None,
                meta: Default::default(),
            }),
            // Commodity.currency + meta
            Directive::Commodity(Commodity {
                date: date(2024, 1, 2),
                currency: "USD".into(),
                meta: commodity_meta.into(),
            }),
            // Balance.amount.currency
            Directive::Balance(Balance {
                date: date(2024, 1, 3),
                account: "Assets:Cash".into(),
                amount: Amount::new(dec!(100), "USD"),
                tolerance: None,
                meta: Default::default(),
            }),
            // Price (both halves)
            Directive::Price(Price {
                date: date(2024, 1, 4),
                currency: "USD".into(),
                amount: Amount::new(dec!(1), "USD"),
                meta: Default::default(),
            }),
            // Transaction with: txn meta (Amount::USD), posting units,
            // cost, price annotation, posting meta.
            Directive::Transaction(Transaction {
                date: date(2024, 1, 5),
                flag: '*',
                payee: None,
                narration: "".into(),
                tags: Default::default(),
                links: Default::default(),
                meta: txn_meta.into(),
                postings: vec![Spanned::synthesized(Posting {
                    account: "Assets:Stock".into(),
                    units: Some(crate::IncompleteAmount::from(Amount::new(dec!(10), "USD"))),
                    cost: Some(Box::new(CostSpec {
                        number: Some(crate::CostNumber::PerUnit { value: dec!(1) }),
                        currency: Some("USD".into()),
                        date: None,
                        label: None,
                        merge: false,
                    })),
                    price: Some(Box::new(PriceAnnotation::unit(Amount::new(dec!(1), "USD")))),
                    flag: None,
                    meta: Default::default(),
                    comments: Default::default(),
                    trailing_comments: Default::default(),
                    booking: Default::default(),
                })],
                trailing_comments: Default::default(),
            }),
            // Custom.values with Currency and Amount variants.
            Directive::Custom(Custom {
                date: date(2024, 1, 6),
                custom_type: "test".into(),
                values: vec![
                    MetaValue::Currency("USD".into()),
                    MetaValue::Amount(Amount::new(dec!(1), "USD")),
                ],
                meta: Default::default(),
            }),
        ];

        let currencies = collect_currencies(&directives);
        let usd_count = currencies.iter().filter(|c| *c == "USD").count();

        // Expected USD visits:
        //   1. Open.currencies[0]
        //   2. Commodity.currency
        //   3. Commodity.meta (`note: USD`)
        //   4. Balance.amount.currency
        //   5. Price.currency
        //   6. Price.amount.currency
        //   7. Transaction.meta (`settled: 1 USD` → Amount.currency)
        //   8. Posting.units (Amount.currency)
        //   9. Posting.cost.currency
        //  10. Posting.price.amount.currency
        //  11. Custom.values[0] (Currency variant)
        //  12. Custom.values[1] (Amount variant)
        assert_eq!(
            usd_count, 12,
            "expected USD visited 12 times across all positions; got {usd_count} in {currencies:?}"
        );
    }

    /// `visit_accounts` must surface every Account-bearing position.
    /// Seeds `Assets:X` into all reachable positions and asserts the
    /// visitor reaches each one.
    #[test]
    fn test_visit_accounts_reaches_every_position() {
        let mut meta_with_account: Metadata = Default::default();
        meta_with_account.insert("see_also", MetaValue::Account("Assets:X".into()));

        let directives = vec![
            Directive::Open(Open {
                date: date(2024, 1, 1),
                account: "Assets:X".into(),
                currencies: vec![],
                booking: None,
                meta: meta_with_account.clone().into(),
            }),
            Directive::Close(Close {
                date: date(2024, 1, 2),
                account: "Assets:X".into(),
                meta: Default::default(),
            }),
            Directive::Balance(Balance {
                date: date(2024, 1, 3),
                account: "Assets:X".into(),
                amount: Amount::new(dec!(0), "USD"),
                tolerance: None,
                meta: Default::default(),
            }),
            Directive::Pad(Pad {
                date: date(2024, 1, 4),
                account: "Assets:X".into(),
                source_account: "Assets:X".into(),
                meta: Default::default(),
            }),
            Directive::Note(Note {
                date: date(2024, 1, 5),
                account: "Assets:X".into(),
                comment: String::new(),
                tags: Default::default(),
                links: Default::default(),
                meta: Default::default(),
            }),
            Directive::Document(Document {
                date: date(2024, 1, 6),
                account: "Assets:X".into(),
                path: String::new(),
                tags: Default::default(),
                links: Default::default(),
                meta: Default::default(),
            }),
            Directive::Transaction(Transaction {
                date: date(2024, 1, 7),
                flag: '*',
                payee: None,
                narration: "".into(),
                tags: Default::default(),
                links: Default::default(),
                meta: meta_with_account.into(),
                postings: vec![Spanned::synthesized(Posting::auto("Assets:X"))],
                trailing_comments: Default::default(),
            }),
            Directive::Custom(Custom {
                date: date(2024, 1, 8),
                custom_type: "test".into(),
                values: vec![MetaValue::Account("Assets:X".into())],
                meta: Default::default(),
            }),
        ];

        let accounts = collect_accounts(&directives);
        let count = accounts.iter().filter(|a| *a == "Assets:X").count();

        // Expected `Assets:X` visits:
        //   1. Open.account
        //   2. Open.meta (`see_also: Assets:X`)
        //   3. Close.account
        //   4. Balance.account
        //   5. Pad.account
        //   6. Pad.source_account
        //   7. Note.account
        //   8. Document.account
        //   9. Transaction.meta (`see_also: Assets:X`)
        //  10. Posting.account
        //  11. Custom.values[0]
        assert_eq!(
            count, 11,
            "expected `Assets:X` visited 11 times; got {count} in {accounts:?}"
        );
    }

    /// `visit_tags` / `visit_links` must surface every Tag/Link-bearing
    /// position. Seeds `proj` (tag) and `inv-1` (link) into all four
    /// reachable positions each and asserts the visitor reaches each.
    #[test]
    fn test_visit_tags_and_links_reach_every_position() {
        use crate::{Link, Tag};

        let mut txn_meta: Metadata = Default::default();
        txn_meta.insert("ref", MetaValue::Tag(Tag::new("proj")));
        txn_meta.insert("see", MetaValue::Link(Link::new("inv-1")));

        let directives = vec![
            // Transaction.tags / Transaction.links + metadata.
            Directive::Transaction(Transaction {
                date: date(2024, 1, 1),
                flag: '*',
                payee: None,
                narration: "".into(),
                tags: vec![Tag::new("proj")].into(),
                links: vec![Link::new("inv-1")].into(),
                meta: txn_meta.into(),
                postings: vec![],
                trailing_comments: Default::default(),
            }),
            // Document.tags / Document.links.
            Directive::Document(Document {
                date: date(2024, 1, 2),
                account: "Assets:Cash".into(),
                path: "x.pdf".into(),
                tags: vec![Tag::new("proj")].into(),
                links: vec![Link::new("inv-1")].into(),
                meta: Default::default(),
            }),
            // Custom.values carrying a Tag and a Link.
            Directive::Custom(Custom {
                date: date(2024, 1, 3),
                custom_type: "test".into(),
                values: vec![
                    MetaValue::Tag(Tag::new("proj")),
                    MetaValue::Link(Link::new("inv-1")),
                ],
                meta: Default::default(),
            }),
        ];

        // Expected `proj` tag visits: Transaction.tags, Transaction.meta,
        // Document.tags, Custom.values = 4. Same shape for `inv-1` link.
        assert_eq!(
            collect_tags(&directives)
                .iter()
                .filter(|t| *t == "proj")
                .count(),
            4,
            "tag `proj` should be visited in all 4 positions"
        );
        assert_eq!(
            collect_links(&directives)
                .iter()
                .filter(|l| *l == "inv-1")
                .count(),
            4,
            "link `inv-1` should be visited in all 4 positions"
        );
    }

    /// `PriceAnnotation` has six variants. The visitor must handle
    /// all of them: Unit / Total emit one currency, the Incomplete
    /// variants emit one if their `IncompleteAmount` has a currency
    /// (`Complete` or `CurrencyOnly`), the Empty variants emit nothing.
    #[test]
    fn test_visit_currencies_handles_all_price_annotation_variants() {
        let txn = |price| Transaction {
            date: date(2024, 1, 1),
            flag: '*',
            payee: None,
            narration: "".into(),
            tags: Default::default(),
            links: Default::default(),
            meta: Default::default(),
            postings: vec![Spanned::synthesized(Posting {
                account: "Assets:X".into(),
                units: Some(crate::IncompleteAmount::from(Amount::new(dec!(1), "AAPL"))),
                cost: None,
                price: Some(Box::new(price)),
                flag: None,
                meta: Default::default(),
                comments: Default::default(),
                trailing_comments: Default::default(),
                booking: Default::default(),
            })],
            trailing_comments: Default::default(),
        };

        // Unit + Total: each surface one currency.
        let unit = Directive::Transaction(txn(PriceAnnotation::unit(Amount::new(dec!(1), "USD"))));
        let total =
            Directive::Transaction(txn(PriceAnnotation::total(Amount::new(dec!(1), "EUR"))));
        // Incomplete-Complete + Incomplete-CurrencyOnly both have a
        // currency; Incomplete-NumberOnly does not.
        let inc_complete = Directive::Transaction(txn(PriceAnnotation::unit_incomplete(
            crate::IncompleteAmount::Complete(Amount::new(dec!(1), "GBP")),
        )));
        let inc_curr = Directive::Transaction(txn(PriceAnnotation::total_incomplete(
            crate::IncompleteAmount::CurrencyOnly("JPY".into()),
        )));
        let inc_num = Directive::Transaction(txn(PriceAnnotation::unit_incomplete(
            crate::IncompleteAmount::NumberOnly(dec!(1)),
        )));
        // Empty variants surface nothing.
        let unit_empty = Directive::Transaction(txn(PriceAnnotation::unit_empty()));
        let total_empty = Directive::Transaction(txn(PriceAnnotation::total_empty()));

        let directives = vec![
            unit,
            total,
            inc_complete,
            inc_curr,
            inc_num,
            unit_empty,
            total_empty,
        ];

        let currencies = collect_currencies(&directives);

        // Each transaction's units side contributes AAPL, so 7×AAPL.
        // Price annotation adds USD/EUR/GBP/JPY for the four non-
        // empty variants; UnitEmpty/TotalEmpty add nothing;
        // NumberOnly adds nothing for its price side.
        let by_curr = |code: &str| currencies.iter().filter(|c| *c == code).count();
        assert_eq!(by_curr("AAPL"), 7);
        assert_eq!(by_curr("USD"), 1);
        assert_eq!(by_curr("EUR"), 1);
        assert_eq!(by_curr("GBP"), 1);
        assert_eq!(by_curr("JPY"), 1);
    }

    /// `visit_numbers` reaches every decimal position, in source order, so a
    /// comparison through it sees each one's scale.
    #[test]
    fn test_visit_numbers_reaches_every_position() {
        let mut meta: Metadata = Default::default();
        meta.insert("first", MetaValue::Number(dec!(1.0)));
        meta.insert("second", MetaValue::Amount(Amount::new(dec!(2.00), "USD")));
        let mut posting = Posting::new("Assets:A", Amount::new(dec!(3.000), "X"))
            .with_cost(CostSpec {
                number: Some(crate::CostNumber::Compound {
                    per_unit: dec!(4),
                    total: dec!(5.5),
                }),
                ..Default::default()
            })
            .with_price(crate::PriceAnnotation::unit(Amount::new(dec!(6.25), "USD")));
        posting.meta = meta.clone().into();
        let txn =
            Transaction::new(date(2024, 1, 1), "t").with_posting(Spanned::synthesized(posting));
        let mut balance = Balance::new(date(2024, 1, 2), "Assets:A", Amount::new(dec!(7), "X"));
        balance.tolerance = Some(dec!(0.01));
        let price = Price::new(date(2024, 1, 3), "X", Amount::new(dec!(8.10), "USD"));
        let mut custom = Custom::new(date(2024, 1, 4), "budget");
        custom.values = vec![
            MetaValue::Number(dec!(9)),
            MetaValue::Amount(Amount::new(dec!(10.5), "USD")),
        ];
        let open = Open::new(date(2024, 1, 5), "Assets:A").with_meta(meta);

        let mut seen = Vec::new();
        for d in [
            Directive::Transaction(txn),
            Directive::Balance(balance),
            Directive::Price(price),
            Directive::Custom(custom),
            Directive::Open(open),
        ] {
            visit_numbers(&d, &mut |n| seen.push(n.to_string()));
        }
        assert_eq!(
            seen,
            [
                "3.000", "4", "5.5", "6.25", "1.0", "2.00", "7", "0.01", "8.10", "9", "10.5",
                "1.0", "2.00"
            ]
        );
    }

    /// `visit_metadata` visits the directive's block, then each posting's.
    #[test]
    fn test_visit_metadata_visits_every_block_in_order() {
        let mut first: Metadata = Default::default();
        first.insert("on_txn", MetaValue::Bool(true));
        let mut second: Metadata = Default::default();
        second.insert("on_posting", MetaValue::Bool(true));
        let mut posting = Posting::new("Assets:A", Amount::new(dec!(1), "X"));
        posting.meta = second.into();
        let mut txn =
            Transaction::new(date(2024, 1, 1), "t").with_posting(Spanned::synthesized(posting));
        txn.meta = first.into();
        let mut keys = Vec::new();
        visit_metadata(&Directive::Transaction(txn), &mut |m| {
            keys.extend(m.keys().map(ToString::to_string));
        });
        assert_eq!(keys, ["on_txn", "on_posting"]);
    }
}
