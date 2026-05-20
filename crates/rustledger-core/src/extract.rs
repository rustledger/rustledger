//! Extract unique accounts, currencies, and payees from directives.
//!
//! These functions are used by both the WASM editor and LSP for completions.

use crate::{Directive, MetaValue, Metadata, PriceAnnotation};

/// Common default currencies included in completions.
pub const DEFAULT_CURRENCIES: &[&str] = &["USD", "EUR", "GBP"];

/// Extract unique account names from directives (sorted, deduplicated).
pub fn extract_accounts(directives: &[Directive]) -> Vec<String> {
    extract_accounts_iter(directives.iter())
}

/// Extract unique account names from an iterator of directive references.
///
/// Use this to avoid cloning when working with `Spanned<Directive>`:
/// ```ignore
/// extract_accounts_iter(parse_result.directives.iter().map(|s| &s.value))
/// ```
/// Extract unique account names from an iterator of directive references.
///
/// Covers every position an account name can appear in source:
/// - `Open.account` / `Close.account`
/// - `Balance.account`
/// - `Pad.account` and `Pad.source_account`
/// - `Note.account`
/// - `Document.account`
/// - `Posting.account` (transactions)
/// - `MetaValue::Account` values inside the metadata block of any
///   directive or posting
/// - `MetaValue::Account` inside `Custom.values`
///
/// Earlier iterations of this function covered only Open / Close /
/// Balance / Pad / Transaction.postings — accounts mentioned only
/// on a Note, Document, in metadata, or in a Custom directive were
/// silently absent from completion suggestions in both the LSP and
/// the WASM editor.
pub fn extract_accounts_iter<'a>(directives: impl Iterator<Item = &'a Directive>) -> Vec<String> {
    let mut accounts = Vec::new();

    for directive in directives {
        match directive {
            Directive::Open(open) => {
                accounts.push(open.account.to_string());
                extract_meta_accounts(&open.meta, &mut accounts);
            }
            Directive::Close(close) => {
                accounts.push(close.account.to_string());
                extract_meta_accounts(&close.meta, &mut accounts);
            }
            Directive::Balance(bal) => {
                accounts.push(bal.account.to_string());
                extract_meta_accounts(&bal.meta, &mut accounts);
            }
            Directive::Pad(pad) => {
                accounts.push(pad.account.to_string());
                accounts.push(pad.source_account.to_string());
                extract_meta_accounts(&pad.meta, &mut accounts);
            }
            Directive::Note(note) => {
                accounts.push(note.account.to_string());
                extract_meta_accounts(&note.meta, &mut accounts);
            }
            Directive::Document(doc) => {
                accounts.push(doc.account.to_string());
                extract_meta_accounts(&doc.meta, &mut accounts);
            }
            Directive::Transaction(txn) => {
                extract_meta_accounts(&txn.meta, &mut accounts);
                for posting in &txn.postings {
                    accounts.push(posting.account.to_string());
                    extract_meta_accounts(&posting.meta, &mut accounts);
                }
            }
            Directive::Custom(custom) => {
                for v in &custom.values {
                    if let MetaValue::Account(a) = v {
                        accounts.push(a.clone());
                    }
                }
                extract_meta_accounts(&custom.meta, &mut accounts);
            }
            Directive::Commodity(comm) => {
                extract_meta_accounts(&comm.meta, &mut accounts);
            }
            Directive::Price(price) => {
                extract_meta_accounts(&price.meta, &mut accounts);
            }
            Directive::Event(event) => {
                extract_meta_accounts(&event.meta, &mut accounts);
            }
            Directive::Query(query) => {
                extract_meta_accounts(&query.meta, &mut accounts);
            }
        }
    }

    accounts.sort();
    accounts.dedup();
    accounts
}

/// Push any account literal embedded in a metadata block onto `out`.
fn extract_meta_accounts(meta: &Metadata, out: &mut Vec<String>) {
    for v in meta.values() {
        if let MetaValue::Account(a) = v {
            out.push(a.clone());
        }
    }
}

/// Extract unique currencies from directives (sorted, deduplicated).
///
/// Includes [`DEFAULT_CURRENCIES`] (USD, EUR, GBP) for completions.
pub fn extract_currencies(directives: &[Directive]) -> Vec<String> {
    extract_currencies_iter(directives.iter())
}

/// Extract unique currencies from an iterator of directive references.
///
/// Covers every position a `Currency` token can appear in source:
/// - `Open.currencies` (constraint list)
/// - `Commodity.currency` (declaration)
/// - `Balance.amount.currency`
/// - `Price` directive (both base `currency` and `amount.currency`)
/// - `Posting.units.currency()` (units side, incl. `CurrencyOnly`)
/// - `Posting.cost.currency` (cost spec)
/// - `Posting.price` (`@`/`@@` annotation, all 6 variants)
/// - `MetaValue::Currency` / `MetaValue::Amount` values inside the
///   metadata block of any directive or posting
/// - `Custom.values` entries that are `MetaValue::Currency` or
///   `MetaValue::Amount` (Custom directives can carry arbitrary
///   `MetaValue`s as positional arguments)
///
/// Earlier iterations of this function covered only `Open`,
/// `Commodity`, `Balance`, and `Posting.units` — any currency that
/// reached the parser through the other positions silently
/// disappeared from completion suggestions in both the LSP and
/// the WASM editor.
pub fn extract_currencies_iter<'a>(directives: impl Iterator<Item = &'a Directive>) -> Vec<String> {
    let mut currencies = Vec::new();

    for directive in directives {
        match directive {
            Directive::Open(open) => {
                for currency in &open.currencies {
                    currencies.push(currency.to_string());
                }
                extract_meta_currencies(&open.meta, &mut currencies);
            }
            Directive::Commodity(comm) => {
                currencies.push(comm.currency.to_string());
                extract_meta_currencies(&comm.meta, &mut currencies);
            }
            Directive::Balance(bal) => {
                currencies.push(bal.amount.currency.to_string());
                extract_meta_currencies(&bal.meta, &mut currencies);
            }
            Directive::Price(price) => {
                currencies.push(price.currency.to_string());
                currencies.push(price.amount.currency.to_string());
                extract_meta_currencies(&price.meta, &mut currencies);
            }
            Directive::Transaction(txn) => {
                extract_meta_currencies(&txn.meta, &mut currencies);
                for posting in &txn.postings {
                    if let Some(ref units) = posting.units
                        && let Some(currency) = units.currency()
                    {
                        currencies.push(currency.to_string());
                    }
                    if let Some(ref cost) = posting.cost
                        && let Some(ref c) = cost.currency
                    {
                        currencies.push(c.to_string());
                    }
                    if let Some(ref price) = posting.price {
                        extract_price_currency(price, &mut currencies);
                    }
                    extract_meta_currencies(&posting.meta, &mut currencies);
                }
            }
            Directive::Custom(custom) => {
                for v in &custom.values {
                    match v {
                        MetaValue::Currency(s) => currencies.push(s.clone()),
                        MetaValue::Amount(a) => currencies.push(a.currency.to_string()),
                        _ => {}
                    }
                }
                extract_meta_currencies(&custom.meta, &mut currencies);
            }
            Directive::Note(note) => {
                extract_meta_currencies(&note.meta, &mut currencies);
            }
            Directive::Document(doc) => {
                extract_meta_currencies(&doc.meta, &mut currencies);
            }
            Directive::Close(close) => {
                extract_meta_currencies(&close.meta, &mut currencies);
            }
            Directive::Pad(pad) => {
                extract_meta_currencies(&pad.meta, &mut currencies);
            }
            Directive::Event(event) => {
                extract_meta_currencies(&event.meta, &mut currencies);
            }
            Directive::Query(query) => {
                extract_meta_currencies(&query.meta, &mut currencies);
            }
        }
    }

    for currency in DEFAULT_CURRENCIES {
        currencies.push((*currency).to_string());
    }

    currencies.sort();
    currencies.dedup();
    currencies
}

/// Push any currency literal embedded in a metadata block onto `out`.
fn extract_meta_currencies(meta: &Metadata, out: &mut Vec<String>) {
    for v in meta.values() {
        match v {
            MetaValue::Currency(s) => out.push(s.clone()),
            MetaValue::Amount(a) => out.push(a.currency.to_string()),
            _ => {}
        }
    }
}

/// Push the currency carried by a `PriceAnnotation` (`@` or `@@`)
/// onto `out`, if it has one. `UnitEmpty` / `TotalEmpty` annotations
/// (the user typed `@`/`@@` without an amount) have no currency.
fn extract_price_currency(price: &PriceAnnotation, out: &mut Vec<String>) {
    match price {
        PriceAnnotation::Unit(a) | PriceAnnotation::Total(a) => {
            out.push(a.currency.to_string());
        }
        PriceAnnotation::UnitIncomplete(ia) | PriceAnnotation::TotalIncomplete(ia) => {
            if let Some(c) = ia.currency() {
                out.push(c.to_string());
            }
        }
        PriceAnnotation::UnitEmpty | PriceAnnotation::TotalEmpty => {}
    }
}

/// Extract unique payees from transactions (sorted, deduplicated).
pub fn extract_payees(directives: &[Directive]) -> Vec<String> {
    extract_payees_iter(directives.iter())
}

/// Extract unique payees from an iterator of directive references.
pub fn extract_payees_iter<'a>(directives: impl Iterator<Item = &'a Directive>) -> Vec<String> {
    let mut payees = Vec::new();

    for directive in directives {
        if let Directive::Transaction(txn) = directive
            && let Some(ref payee) = txn.payee
        {
            payees.push(payee.to_string());
        }
    }

    payees.sort();
    payees.dedup();
    payees
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::NaiveDate;
    use crate::{Amount, Balance, Commodity, Open, Pad, Posting, Transaction};

    fn date(y: i32, m: u32, d: u32) -> NaiveDate {
        crate::naive_date(y, m, d).unwrap()
    }

    fn test_directives() -> Vec<Directive> {
        vec![
            Directive::Open(Open {
                date: date(2024, 1, 1),
                account: "Assets:Cash".into(),
                currencies: vec!["USD".into(), "EUR".into()],
                booking: None,
                meta: Default::default(),
            }),
            Directive::Open(Open {
                date: date(2024, 1, 1),
                account: "Expenses:Food".into(),
                currencies: vec![],
                booking: None,
                meta: Default::default(),
            }),
            Directive::Commodity(Commodity {
                date: date(2024, 1, 1),
                currency: "BTC".into(),
                meta: Default::default(),
            }),
            Directive::Pad(Pad {
                date: date(2024, 1, 2),
                account: "Assets:Cash".into(),
                source_account: "Equity:Opening".into(),
                meta: Default::default(),
            }),
            Directive::Balance(Balance {
                date: date(2024, 1, 3),
                account: "Assets:Cash".into(),
                amount: Amount::new(rust_decimal_macros::dec!(100), "CHF"),
                tolerance: None,
                meta: Default::default(),
            }),
            Directive::Transaction(Transaction {
                date: date(2024, 1, 4),
                flag: '*',
                payee: Some("Corner Store".into()),
                narration: "Groceries".into(),
                tags: vec![],
                links: vec![],
                meta: Default::default(),
                postings: vec![
                    crate::Spanned::synthesized(Posting {
                        account: "Expenses:Food".into(),
                        units: Some(crate::IncompleteAmount::from(Amount::new(
                            rust_decimal_macros::dec!(25),
                            "USD",
                        ))),
                        cost: None,
                        price: None,
                        flag: None,
                        meta: Default::default(),
                        comments: vec![],
                        trailing_comments: vec![],
                    }),
                    crate::Spanned::synthesized(Posting {
                        account: "Assets:Cash".into(),
                        units: None,
                        cost: None,
                        price: None,
                        flag: None,
                        meta: Default::default(),
                        comments: vec![],
                        trailing_comments: vec![],
                    }),
                ],
                trailing_comments: vec![],
            }),
            Directive::Transaction(Transaction {
                date: date(2024, 1, 5),
                flag: '*',
                payee: Some("Coffee Shop".into()),
                narration: "Coffee".into(),
                tags: vec![],
                links: vec![],
                meta: Default::default(),
                postings: vec![],
                trailing_comments: vec![],
            }),
        ]
    }

    #[test]
    fn test_empty_directives() {
        let empty: Vec<Directive> = vec![];
        assert!(extract_accounts(&empty).is_empty());
        assert_eq!(extract_currencies(&empty).len(), DEFAULT_CURRENCIES.len());
        assert!(extract_payees(&empty).is_empty());
    }

    #[test]
    fn test_extract_accounts_from_directives() {
        let directives = test_directives();
        let accounts = extract_accounts(&directives);
        assert_eq!(
            accounts,
            vec![
                "Assets:Cash".to_string(),
                "Equity:Opening".to_string(),
                "Expenses:Food".to_string(),
            ]
        );
    }

    #[test]
    fn test_extract_currencies_from_directives() {
        let directives = test_directives();
        let currencies = extract_currencies(&directives);
        // BTC from Commodity, CHF from Balance, EUR+USD from Open, defaults GBP
        assert!(currencies.contains(&"BTC".to_string()));
        assert!(currencies.contains(&"CHF".to_string()));
        assert!(currencies.contains(&"EUR".to_string()));
        assert!(currencies.contains(&"GBP".to_string()));
        assert!(currencies.contains(&"USD".to_string()));
    }

    #[test]
    fn test_extract_payees_from_directives() {
        let directives = test_directives();
        let payees = extract_payees(&directives);
        assert_eq!(
            payees,
            vec!["Coffee Shop".to_string(), "Corner Store".to_string()]
        );
    }

    #[test]
    fn test_default_currencies_not_duplicated() {
        // Directives already contain USD and EUR from Open currencies
        let directives = test_directives();
        let currencies = extract_currencies(&directives);
        assert_eq!(
            currencies.iter().filter(|c| *c == "USD").count(),
            1,
            "USD should appear exactly once"
        );
    }

    #[test]
    fn test_iter_variant_matches_slice_variant() {
        let directives = test_directives();
        assert_eq!(
            extract_accounts(&directives),
            extract_accounts_iter(directives.iter())
        );
        assert_eq!(
            extract_currencies(&directives),
            extract_currencies_iter(directives.iter())
        );
        assert_eq!(
            extract_payees(&directives),
            extract_payees_iter(directives.iter())
        );
    }

    /// Regression test: currencies that reach the parser via
    /// positions OTHER than `Open` / `Commodity` / `Balance` /
    /// `Posting.units` must still appear in the extraction list.
    ///
    /// The earlier implementation walked only those four positions
    /// and silently dropped currencies from cost specs, price
    /// annotations, `Price` directives, metadata values, and Custom
    /// directive arguments — which meant completion suggestions in
    /// both the LSP and WASM editor were missing real currencies
    /// the user had typed.
    #[test]
    fn test_extract_currencies_covers_cost_price_meta_custom() {
        use crate::{CostSpec, Custom, Price, PriceAnnotation};
        use rust_decimal_macros::dec;

        // CAD in transaction metadata as MetaValue::Currency.
        // KRW in posting metadata as MetaValue::Amount.
        let mut txn_meta: Metadata = Default::default();
        txn_meta.insert(
            "fx_pair".to_string(),
            MetaValue::Currency("CAD".to_string()),
        );
        let mut posting_meta: Metadata = Default::default();
        posting_meta.insert(
            "settled".to_string(),
            MetaValue::Amount(Amount::new(dec!(120000), "KRW")),
        );

        let directives = vec![
            // One transaction exercising four positions at once:
            // cost spec (JPY), `@` annotation (CHF), txn meta (CAD),
            // posting meta (KRW).
            Directive::Transaction(Transaction {
                date: date(2024, 1, 1),
                flag: '*',
                payee: None,
                narration: "".into(),
                tags: vec![],
                links: vec![],
                meta: txn_meta,
                postings: vec![crate::Spanned::synthesized(Posting {
                    account: "Assets:Stock".into(),
                    units: Some(crate::IncompleteAmount::from(Amount::new(dec!(10), "AAPL"))),
                    cost: Some(CostSpec {
                        number_per: Some(dec!(150)),
                        number_total: None,
                        currency: Some("JPY".into()),
                        date: None,
                        label: None,
                        merge: false,
                    }),
                    price: Some(PriceAnnotation::Unit(Amount::new(dec!(1.1), "CHF"))),
                    flag: None,
                    meta: posting_meta,
                    comments: vec![],
                    trailing_comments: vec![],
                })],
                trailing_comments: vec![],
            }),
            // Price directive carrying both AAPL (base) and SGD (amount).
            Directive::Price(Price {
                date: date(2024, 1, 3),
                currency: "AAPL".into(),
                amount: Amount::new(dec!(200), "SGD"),
                meta: Default::default(),
            }),
            // Custom directive arguments include MXN (Currency)
            // and TWD (inside an Amount).
            Directive::Custom(Custom {
                date: date(2024, 1, 4),
                custom_type: "fx_corridors".to_string(),
                values: vec![
                    MetaValue::Currency("MXN".to_string()),
                    MetaValue::Amount(Amount::new(dec!(30), "TWD")),
                ],
                meta: Default::default(),
            }),
        ];

        let currencies = extract_currencies(&directives);

        for expected in [
            "JPY", "CHF", "SGD", "AAPL", // cost / @ / Price directive (both halves)
            "CAD", "KRW", // transaction-meta / posting-meta
            "MXN", "TWD", // Custom.values (Currency + Amount)
        ] {
            assert!(
                currencies.contains(&expected.to_string()),
                "expected {expected} in extracted currencies; got {currencies:?}"
            );
        }
    }

    /// Regression test: account names that reach the parser via
    /// positions OTHER than `Open` / `Close` / `Balance` / `Pad` /
    /// `Posting.account` must still appear in the extraction list.
    ///
    /// The pre-fix walk missed `Note.account`, `Document.account`,
    /// `MetaValue::Account` in metadata blocks, and `Custom.values`
    /// account entries — meaning completion suggestions in both the
    /// LSP and WASM editor were missing real accounts the user had
    /// referenced.
    #[test]
    fn test_extract_accounts_covers_note_document_meta_custom() {
        use crate::{Custom, Document, Note};
        let mut txn_meta: Metadata = Default::default();
        txn_meta.insert(
            "partner".to_string(),
            MetaValue::Account("Assets:JointAccount".into()),
        );

        let directives = vec![
            // Note carrying an account the user has never opened elsewhere.
            Directive::Note(Note {
                date: date(2024, 1, 1),
                account: "Assets:OldCheckingArchive".into(),
                comment: "reconcile end of year".to_string(),
                meta: Default::default(),
            }),
            // Document carrying another fresh account.
            Directive::Document(Document {
                date: date(2024, 1, 2),
                account: "Liabilities:CreditCard:CitiBank".into(),
                path: "statement.pdf".to_string(),
                tags: vec![],
                links: vec![],
                meta: Default::default(),
            }),
            // Transaction whose metadata carries an account reference.
            Directive::Transaction(Transaction {
                date: date(2024, 1, 3),
                flag: '*',
                payee: None,
                narration: "".into(),
                tags: vec![],
                links: vec![],
                meta: txn_meta,
                postings: vec![],
                trailing_comments: vec![],
            }),
            // Custom directive whose values include an Account.
            Directive::Custom(Custom {
                date: date(2024, 1, 4),
                custom_type: "budget".to_string(),
                values: vec![MetaValue::Account("Expenses:Groceries:Whole".into())],
                meta: Default::default(),
            }),
        ];

        let accounts = extract_accounts(&directives);

        for expected in [
            "Assets:OldCheckingArchive",
            "Liabilities:CreditCard:CitiBank",
            "Assets:JointAccount",
            "Expenses:Groceries:Whole",
        ] {
            assert!(
                accounts.contains(&expected.to_string()),
                "expected {expected} in extracted accounts (covers Note/Document/meta/Custom arms); got {accounts:?}"
            );
        }
    }
}
