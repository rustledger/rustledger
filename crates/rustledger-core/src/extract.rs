//! Extract unique accounts, currencies, and payees from directives.
//!
//! These functions are used by both the WASM editor and LSP for completions.

use crate::Directive;

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
pub fn extract_accounts_iter<'a>(directives: impl Iterator<Item = &'a Directive>) -> Vec<String> {
    let mut accounts = Vec::new();

    for directive in directives {
        match directive {
            Directive::Open(open) => accounts.push(open.account.to_string()),
            Directive::Close(close) => accounts.push(close.account.to_string()),
            Directive::Balance(bal) => accounts.push(bal.account.to_string()),
            Directive::Pad(pad) => {
                accounts.push(pad.account.to_string());
                accounts.push(pad.source_account.to_string());
            }
            Directive::Transaction(txn) => {
                for posting in &txn.postings {
                    accounts.push(posting.account.to_string());
                }
            }
            _ => {}
        }
    }

    accounts.sort();
    accounts.dedup();
    accounts
}

/// Extract unique currencies from directives (sorted, deduplicated).
///
/// Includes [`DEFAULT_CURRENCIES`] (USD, EUR, GBP) for completions.
pub fn extract_currencies(directives: &[Directive]) -> Vec<String> {
    extract_currencies_iter(directives.iter())
}

/// Extract unique currencies from an iterator of directive references.
pub fn extract_currencies_iter<'a>(directives: impl Iterator<Item = &'a Directive>) -> Vec<String> {
    let mut currencies = Vec::new();

    for directive in directives {
        match directive {
            Directive::Open(open) => {
                for currency in &open.currencies {
                    currencies.push(currency.to_string());
                }
            }
            Directive::Commodity(comm) => currencies.push(comm.currency.to_string()),
            Directive::Balance(bal) => currencies.push(bal.amount.currency.to_string()),
            Directive::Transaction(txn) => {
                for posting in &txn.postings {
                    if let Some(ref units) = posting.units
                        && let Some(currency) = units.currency()
                    {
                        currencies.push(currency.to_string());
                    }
                }
            }
            _ => {}
        }
    }

    for currency in DEFAULT_CURRENCIES {
        currencies.push((*currency).to_string());
    }

    currencies.sort();
    currencies.dedup();
    currencies
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
}
