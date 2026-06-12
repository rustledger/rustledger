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

use crate::{Directive, IncompleteAmount, MetaValue, Metadata, PriceAnnotation};

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
/// source for the parser-generated AST, except for metadata (which
/// is a `HashMap` and has unspecified iteration order).
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
/// AST, except for metadata (unspecified iteration order).
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
/// - `MetaValue::Tag` in any directive's or posting's metadata
/// - `Custom.values` entries that are `MetaValue::Tag`
///
/// Visit order matches the source order of the parser-generated AST,
/// except for metadata (unspecified iteration order).
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
        Directive::Note(note) => visit_meta_tags(&note.meta, visit),
        Directive::Price(price) => visit_meta_tags(&price.meta, visit),
        Directive::Event(event) => visit_meta_tags(&event.meta, visit),
        Directive::Query(query) => visit_meta_tags(&query.meta, visit),
    }
}

/// Walk every position a link can appear in this directive, invoking
/// `visit` once per occurrence (link text without the `^` sigil).
///
/// Positions covered mirror [`visit_tags`], with `Link` in place of
/// `Tag`: `Transaction.links`, `Document.links`, `MetaValue::Link` in
/// metadata, and `Custom.values` link entries.
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
        Directive::Note(note) => visit_meta_links(&note.meta, visit),
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
        commodity_meta.insert("note".into(), MetaValue::Currency("USD".into()));

        let mut txn_meta: Metadata = Default::default();
        txn_meta.insert(
            "settled".into(),
            MetaValue::Amount(Amount::new(dec!(1), "USD")),
        );

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
                meta: commodity_meta,
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
                tags: vec![],
                links: vec![],
                meta: txn_meta,
                postings: vec![Spanned::synthesized(Posting {
                    account: "Assets:Stock".into(),
                    units: Some(crate::IncompleteAmount::from(Amount::new(dec!(10), "USD"))),
                    cost: Some(CostSpec {
                        number: Some(crate::CostNumber::PerUnit { value: dec!(1) }),
                        currency: Some("USD".into()),
                        date: None,
                        label: None,
                        merge: false,
                    }),
                    price: Some(PriceAnnotation::unit(Amount::new(dec!(1), "USD"))),
                    flag: None,
                    meta: Default::default(),
                    comments: vec![],
                    trailing_comments: vec![],
                })],
                trailing_comments: vec![],
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
        meta_with_account.insert("see_also".into(), MetaValue::Account("Assets:X".into()));

        let directives = vec![
            Directive::Open(Open {
                date: date(2024, 1, 1),
                account: "Assets:X".into(),
                currencies: vec![],
                booking: None,
                meta: meta_with_account.clone(),
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
                meta: Default::default(),
            }),
            Directive::Document(Document {
                date: date(2024, 1, 6),
                account: "Assets:X".into(),
                path: String::new(),
                tags: vec![],
                links: vec![],
                meta: Default::default(),
            }),
            Directive::Transaction(Transaction {
                date: date(2024, 1, 7),
                flag: '*',
                payee: None,
                narration: "".into(),
                tags: vec![],
                links: vec![],
                meta: meta_with_account,
                postings: vec![Spanned::synthesized(Posting::auto("Assets:X"))],
                trailing_comments: vec![],
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
        txn_meta.insert("ref".into(), MetaValue::Tag(Tag::new("proj")));
        txn_meta.insert("see".into(), MetaValue::Link(Link::new("inv-1")));

        let directives = vec![
            // Transaction.tags / Transaction.links + metadata.
            Directive::Transaction(Transaction {
                date: date(2024, 1, 1),
                flag: '*',
                payee: None,
                narration: "".into(),
                tags: vec![Tag::new("proj")],
                links: vec![Link::new("inv-1")],
                meta: txn_meta,
                postings: vec![],
                trailing_comments: vec![],
            }),
            // Document.tags / Document.links.
            Directive::Document(Document {
                date: date(2024, 1, 2),
                account: "Assets:Cash".into(),
                path: "x.pdf".into(),
                tags: vec![Tag::new("proj")],
                links: vec![Link::new("inv-1")],
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
            tags: vec![],
            links: vec![],
            meta: Default::default(),
            postings: vec![Spanned::synthesized(Posting {
                account: "Assets:X".into(),
                units: Some(crate::IncompleteAmount::from(Amount::new(dec!(1), "AAPL"))),
                cost: None,
                price: Some(price),
                flag: None,
                meta: Default::default(),
                comments: vec![],
                trailing_comments: vec![],
            })],
            trailing_comments: vec![],
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
}
