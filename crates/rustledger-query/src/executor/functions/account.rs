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
    pub(crate) fn account_type_index(&self, account: &str) -> u8 {
        // Classify against the CONFIGURED account types (honors `name_*`
        // renames — beanquery's account_sortkey does too; the previous
        // ACCOUNT_TYPES-const lookup sorted renamed roots as "custom"/5).
        self.account_types.sort_index(account)
    }
}
