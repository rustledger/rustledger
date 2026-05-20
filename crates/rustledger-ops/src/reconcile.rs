//! Balance reconciliation.
//!
//! Compares imported transactions against a known statement ending balance
//! to verify that all transactions were captured correctly. Generates
//! balance assertion directives for the ledger.

use rust_decimal::Decimal;
use rustledger_plugin_types::{
    AmountData, BalanceData, DirectiveData, DirectiveWrapper, MetaValueData,
};
use std::str::FromStr;

/// A balance point extracted from a bank statement.
#[derive(Debug, Clone)]
pub struct StatementBalance {
    /// Date of the balance (usually end of statement period).
    pub date: String,
    /// Account this balance applies to.
    pub account: String,
    /// The balance amount.
    pub number: Decimal,
    /// Currency.
    pub currency: String,
}

/// Result of reconciling transactions against a statement balance.
#[derive(Debug)]
pub struct ReconciliationResult {
    /// Whether the computed balance matches the statement balance.
    pub matches: bool,
    /// The expected balance (from the statement).
    pub expected: Decimal,
    /// The computed balance (sum of all transaction postings for the account).
    pub computed: Decimal,
    /// The difference (expected - computed).
    pub difference: Decimal,
    /// A balance assertion directive to add to the ledger.
    pub balance_directive: DirectiveWrapper,
}

/// Reconcile imported transactions against a statement ending balance.
///
/// Computes the sum of all postings to the specified account and compares
/// against the expected ending balance. Returns the result including a
/// balance assertion directive that can be appended to the ledger.
///
/// `opening_balance` is the account balance before the imported transactions
/// (if known). If `None`, only the transaction total is compared.
#[must_use]
pub fn reconcile(
    directives: &[DirectiveWrapper],
    ending_balance: &StatementBalance,
    opening_balance: Option<Decimal>,
) -> ReconciliationResult {
    let mut total = opening_balance.unwrap_or(Decimal::ZERO);

    for d in directives {
        if let DirectiveData::Transaction(txn) = &d.data {
            for posting in &txn.postings {
                if posting.account == ending_balance.account
                    && let Some(units) = &posting.units
                    && units.currency == ending_balance.currency
                    && let Ok(amount) = Decimal::from_str(&units.number)
                {
                    total += amount;
                }
            }
        }
    }

    let difference = ending_balance.number - total;
    let matches = difference.abs() < Decimal::new(1, 2); // Within 0.01

    let balance_directive = create_balance_directive(ending_balance);

    ReconciliationResult {
        matches,
        expected: ending_balance.number,
        computed: total,
        difference,
        balance_directive,
    }
}

/// Create a balance assertion directive from a statement balance.
#[must_use]
pub fn create_balance_directive(balance: &StatementBalance) -> DirectiveWrapper {
    DirectiveWrapper {
        directive_type: "balance".to_string(),
        date: balance.date.clone(),
        filename: Some("<import-reconcile>".to_string()),
        lineno: None,
        data: DirectiveData::Balance(BalanceData {
            account: balance.account.clone(),
            amount: AmountData {
                number: balance.number.to_string(),
                currency: balance.currency.clone(),
            },
            tolerance: None,
            metadata: vec![("import-reconcile".to_string(), MetaValueData::Bool(true))],
        }),
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use rustledger_plugin_types::{PostingData, TransactionData};

    fn make_txn(date: &str, account: &str, amount: &str, currency: &str) -> DirectiveWrapper {
        DirectiveWrapper {
            directive_type: "transaction".to_string(),
            date: date.to_string(),
            filename: None,
            lineno: None,
            data: DirectiveData::Transaction(TransactionData {
                flag: "*".to_string(),
                payee: None,
                narration: "Test".to_string(),
                tags: vec![],
                links: vec![],
                metadata: vec![],
                postings: vec![
                    PostingData {
                        account: account.to_string(),
                        units: Some(AmountData {
                            number: amount.to_string(),
                            currency: currency.to_string(),
                        }),
                        cost: None,
                        price: None,
                        flag: None,
                        metadata: vec![],
                        span: None,
                    },
                    PostingData {
                        account: "Expenses:Unknown".to_string(),
                        units: None,
                        cost: None,
                        price: None,
                        flag: None,
                        metadata: vec![],
                        span: None,
                    },
                ],
            }),
        }
    }

    #[test]
    fn reconcile_matches() {
        let directives = vec![
            make_txn("2024-01-15", "Assets:Checking", "-50.00", "USD"),
            make_txn("2024-01-16", "Assets:Checking", "-30.00", "USD"),
            make_txn("2024-01-17", "Assets:Checking", "100.00", "USD"),
        ];
        let balance = StatementBalance {
            date: "2024-01-31".to_string(),
            account: "Assets:Checking".to_string(),
            number: Decimal::new(102_000, 2), // 1020.00 (opening 1000 + 20 net)
            currency: "USD".to_string(),
        };
        let result = reconcile(&directives, &balance, Some(Decimal::new(100_000, 2)));
        assert!(result.matches);
        assert_eq!(result.difference, Decimal::ZERO);
    }

    #[test]
    fn reconcile_mismatch() {
        let directives = vec![make_txn("2024-01-15", "Assets:Checking", "-50.00", "USD")];
        let balance = StatementBalance {
            date: "2024-01-31".to_string(),
            account: "Assets:Checking".to_string(),
            number: Decimal::new(100_000, 2), // 1000.00
            currency: "USD".to_string(),
        };
        // Opening 1000, spent 50, should be 950 but statement says 1000
        let result = reconcile(&directives, &balance, Some(Decimal::new(100_000, 2)));
        assert!(!result.matches);
        assert_eq!(result.difference, Decimal::new(5000, 2)); // 50.00
    }

    #[test]
    fn reconcile_no_opening_balance() {
        let directives = vec![
            make_txn("2024-01-15", "Assets:Checking", "-50.00", "USD"),
            make_txn("2024-01-16", "Assets:Checking", "100.00", "USD"),
        ];
        let balance = StatementBalance {
            date: "2024-01-31".to_string(),
            account: "Assets:Checking".to_string(),
            number: Decimal::new(5000, 2), // 50.00
            currency: "USD".to_string(),
        };
        let result = reconcile(&directives, &balance, None);
        assert!(result.matches);
    }

    #[test]
    fn reconcile_ignores_other_accounts() {
        let directives = vec![
            make_txn("2024-01-15", "Assets:Checking", "-50.00", "USD"),
            make_txn("2024-01-15", "Assets:Savings", "50.00", "USD"),
        ];
        let balance = StatementBalance {
            date: "2024-01-31".to_string(),
            account: "Assets:Checking".to_string(),
            number: Decimal::new(-5000, 2), // -50.00
            currency: "USD".to_string(),
        };
        let result = reconcile(&directives, &balance, None);
        assert!(result.matches);
    }

    #[test]
    fn balance_directive_created() {
        let balance = StatementBalance {
            date: "2024-01-31".to_string(),
            account: "Assets:Checking".to_string(),
            number: Decimal::new(100_000, 2),
            currency: "USD".to_string(),
        };
        let directive = create_balance_directive(&balance);
        assert_eq!(directive.date, "2024-01-31");
        if let DirectiveData::Balance(b) = &directive.data {
            assert_eq!(b.account, "Assets:Checking");
            assert_eq!(b.amount.number, "1000.00");
            assert_eq!(b.amount.currency, "USD");
        } else {
            panic!("Expected Balance directive");
        }
    }

    #[test]
    fn balance_directive_has_metadata() {
        let balance = StatementBalance {
            date: "2024-01-31".to_string(),
            account: "Assets:Checking".to_string(),
            number: Decimal::new(100_000, 2),
            currency: "USD".to_string(),
        };
        let directive = create_balance_directive(&balance);
        if let DirectiveData::Balance(b) = &directive.data {
            assert!(b.metadata.iter().any(|(k, _)| k == "import-reconcile"));
        }
    }
}
