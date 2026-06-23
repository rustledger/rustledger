//! Account function implementations for the BQL executor.

use super::super::Executor;

impl Executor<'_> {
    /// Get the account type index for sorting.
    ///
    /// Returns the type index matching Python beancount:
    /// - Assets = 0
    /// - Liabilities = 1
    /// - Equity = 2
    /// - Income = 3
    /// - Expenses = 4
    /// - Other = 5 (for custom account types)
    pub(crate) fn account_type_index(account: &str) -> u8 {
        // Extract the first component (root account type) and look it up in the
        // canonical root list (`rustledger_core::ACCOUNT_TYPES`); custom types
        // (not in the list) sort last.
        let root = account.split(':').next().unwrap_or(account);
        rustledger_core::ACCOUNT_TYPES
            .iter()
            .position(|t| *t == root)
            .map_or(5, |i| i as u8)
    }
}
