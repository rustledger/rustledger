//! Balance reconciliation.
//!
//! Compares imported transactions against a known statement ending balance
//! to verify that all transactions were captured correctly. Generates
//! balance assertion directives for the ledger.

use rust_decimal::Decimal;
use rustledger_core::{Amount, Balance, Directive, MetaValue, Metadata, NaiveDate};

/// A balance point extracted from a bank statement.
#[derive(Debug, Clone)]
pub struct StatementBalance {
    /// Date of the balance (usually end of statement period).
    pub date: NaiveDate,
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
    pub balance_directive: Directive,
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
    directives: &[Directive],
    ending_balance: &StatementBalance,
    opening_balance: Option<Decimal>,
) -> ReconciliationResult {
    let mut total = opening_balance.unwrap_or(Decimal::ZERO);

    for d in directives {
        if let Directive::Transaction(txn) = d {
            for posting in &txn.postings {
                if posting.account.as_str() == ending_balance.account
                    && let Some(units) = posting.amount()
                    && units.currency.as_str() == ending_balance.currency
                {
                    total += units.number;
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

/// Create a core balance-assertion [`Directive`] from a statement balance.
///
/// Returns a [`Directive`] directly so the CLI can append it without a
/// `DirectiveWrapper` round-trip (it previously built a wrapper here only to call
/// `wrapper_to_directive` on it one line later).
#[must_use]
pub fn create_balance_directive(balance: &StatementBalance) -> Directive {
    let amount = Amount::new(balance.number, balance.currency.as_str());
    let mut meta = Metadata::default();
    meta.insert("import-reconcile".to_string(), MetaValue::Bool(true));
    Directive::Balance(Balance::new(balance.date, balance.account.as_str(), amount).with_meta(meta))
}

#[cfg(test)]
mod tests {
    use super::*;
    use rustledger_core::{Posting, Transaction};

    fn make_txn(date: &str, account: &str, amount: &str, currency: &str) -> Directive {
        let txn = Transaction::new(date.parse::<NaiveDate>().unwrap(), "Test")
            .with_synthesized_posting(Posting::new(
                account,
                Amount::new(amount.parse::<Decimal>().unwrap(), currency),
            ))
            .with_synthesized_posting(Posting::auto("Expenses:Unknown"));
        Directive::Transaction(txn)
    }

    #[test]
    fn reconcile_matches() {
        let directives = vec![
            make_txn("2024-01-15", "Assets:Checking", "-50.00", "USD"),
            make_txn("2024-01-16", "Assets:Checking", "-30.00", "USD"),
            make_txn("2024-01-17", "Assets:Checking", "100.00", "USD"),
        ];
        let balance = StatementBalance {
            date: "2024-01-31".parse().unwrap(),
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
            date: "2024-01-31".parse().unwrap(),
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
            date: "2024-01-31".parse().unwrap(),
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
            date: "2024-01-31".parse().unwrap(),
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
            date: "2024-01-31".parse().unwrap(),
            account: "Assets:Checking".to_string(),
            number: Decimal::new(100_000, 2),
            currency: "USD".to_string(),
        };
        let directive = create_balance_directive(&balance);
        if let Directive::Balance(b) = &directive {
            assert_eq!(b.date, "2024-01-31".parse::<NaiveDate>().unwrap());
            assert_eq!(b.account.as_str(), "Assets:Checking");
            assert_eq!(b.amount.number, Decimal::new(100_000, 2));
            assert_eq!(b.amount.currency.as_str(), "USD");
        } else {
            panic!("Expected Balance directive");
        }
    }

    #[test]
    fn balance_directive_has_metadata() {
        let balance = StatementBalance {
            date: "2024-01-31".parse().unwrap(),
            account: "Assets:Checking".to_string(),
            number: Decimal::new(100_000, 2),
            currency: "USD".to_string(),
        };
        let directive = create_balance_directive(&balance);
        if let Directive::Balance(b) = &directive {
            assert!(b.meta.contains_key("import-reconcile"));
        } else {
            panic!("Expected Balance directive");
        }
    }
}
