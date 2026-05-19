//! ML-based account suggestion for `rledger extract --suggest-categories`.
//!
//! Trains a Multinomial Naive Bayes classifier on the user's existing ledger
//! and replaces fallback contra-accounts (`Expenses:Unknown`, `Income:Unknown`)
//! on imported transactions with the model's top prediction.
//!
//! This is the fallback path *after* the rules engine. Transactions with
//! explicit rule matches keep their rule-assigned account; only unmatched
//! transactions get ML treatment.
//!
//! Predictions are uncalibrated — see `rustledger_ops::ml::CategorizationModel`.

use anyhow::{Context, Result, anyhow};
use rustledger_core::{Directive, InternedStr, Transaction};
use rustledger_ops::ml::CategorizationModel;
use rustledger_plugin::convert::directives_to_wrappers;

/// Outcome of running ML suggestion over a batch of imported directives.
#[derive(Debug, Default)]
pub(super) struct SuggestStats {
    /// Number of transactions whose contra-account was changed by ML.
    pub modified: usize,
    /// Number of transactions inspected (i.e., matched a fallback account).
    pub inspected: usize,
}

/// Train a model from `existing_txns` and rewrite the contra-account on any
/// transaction in `directives` whose second posting matches one of the
/// `fallback_accounts`. The caller supplies the fallback list — for CSV
/// imports this comes from `CsvConfig::default_expense` /
/// `default_income` (defaulting to `Expenses:Unknown` / `Income:Unknown`);
/// for OFX it's the importer's hardcoded `Expenses:Unknown`.
///
/// Returns counts of inspected / modified transactions. The caller is expected
/// to print a summary line.
///
/// Returns an error only if training fails for non-recoverable reasons.
/// `InsufficientData` is treated as a no-op (with a warning to stderr) since
/// it's expected when the user has a small or new ledger.
pub(super) fn apply_ml_suggestions(
    directives: &mut [Directive],
    existing_txns: &[Transaction],
    fallback_accounts: &[String],
) -> Result<SuggestStats> {
    // Wrap existing transactions as Directives for the wrapper-based ML API.
    // Clone is unavoidable here — `existing_txns` is also used for duplicate
    // detection in the calling path.
    let training_directives: Vec<Directive> = existing_txns
        .iter()
        .cloned()
        .map(Directive::Transaction)
        .collect();
    let training_wrappers = directives_to_wrappers(&training_directives);

    let model = match CategorizationModel::train(&training_wrappers) {
        Ok(m) => m,
        Err(rustledger_ops::ml::MlError::InsufficientData(reason)) => {
            eprintln!(
                "warning: --suggest-categories: insufficient training data ({reason}); skipping ML suggestions"
            );
            return Ok(SuggestStats::default());
        }
        Err(e) => return Err(anyhow!("ML training failed: {e}")),
    };

    let mut stats = SuggestStats::default();

    for directive in directives.iter_mut() {
        let Directive::Transaction(txn) = directive else {
            continue;
        };

        // Only re-categorize when the second posting is a fallback account.
        // Transactions with explicit rule matches keep their rule-assigned
        // contra-account.
        let Some(contra) = txn.postings.get(1) else {
            continue;
        };
        if !fallback_accounts
            .iter()
            .any(|fb| contra.account.as_str() == fb)
        {
            continue;
        }
        stats.inspected += 1;

        let payee = txn.payee.as_ref().map(InternedStr::as_str);
        let narration = txn.narration.as_str();
        let predictions = model.predict(narration, payee);

        if let Some((predicted, _conf)) = predictions.into_iter().next() {
            // `predict` returns at most one prediction with non-zero
            // confidence; if the predicted account differs from the
            // fallback, rewrite it.
            if predicted != contra.account.as_str() {
                txn.postings[1].account = InternedStr::from(predicted);
                stats.modified += 1;
            }
        }
    }

    Ok(stats)
}

/// Convenience wrapper: prints a one-line summary to stderr.
pub(super) fn apply_ml_suggestions_with_summary(
    directives: &mut [Directive],
    existing_txns: &[Transaction],
    fallback_accounts: &[String],
) -> Result<()> {
    let stats = apply_ml_suggestions(directives, existing_txns, fallback_accounts)
        .context("applying ML category suggestions")?;
    if stats.inspected > 0 {
        eprintln!(
            "ML suggestions: re-categorized {}/{} fallback transaction(s)",
            stats.modified, stats.inspected
        );
    }
    Ok(())
}

#[cfg(test)]
mod tests {
    use super::*;
    use rust_decimal::Decimal;
    use rustledger_core::{Amount, Posting, Transaction, naive_date};

    fn txn(payee: &str, narration: &str, contra_account: &str, amount: i64) -> Transaction {
        let mut t = Transaction::new(naive_date(2025, 1, 15).unwrap(), narration);
        t.payee = Some(payee.into());
        t.with_synthesized_posting(Posting::new(
            "Assets:Bank",
            Amount::new(Decimal::from(-amount), "USD"),
        ))
        .with_synthesized_posting(Posting::auto(contra_account))
    }

    fn training_set() -> Vec<Transaction> {
        vec![
            txn("Whole Foods", "Groceries", "Expenses:Groceries", 50),
            txn("Trader Joes", "Weekly food", "Expenses:Groceries", 60),
            txn("Safeway", "Groceries", "Expenses:Groceries", 45),
            txn("Kroger", "Food", "Expenses:Groceries", 70),
            txn("Starbucks", "Coffee", "Expenses:Dining", 8),
            txn("Chipotle", "Lunch", "Expenses:Dining", 12),
            txn("McDonalds", "Lunch", "Expenses:Dining", 9),
            txn("Shell", "Gas", "Expenses:Transport", 40),
            txn("Chevron", "Fuel", "Expenses:Transport", 35),
            txn("Uber", "Ride", "Expenses:Transport", 20),
        ]
    }

    fn default_fallbacks() -> Vec<String> {
        vec!["Expenses:Unknown".to_string(), "Income:Unknown".to_string()]
    }

    #[test]
    fn rewrites_fallback_account() {
        let existing = training_set();
        let mut new_directives = vec![Directive::Transaction(txn(
            "Whole Foods",
            "Groceries",
            "Expenses:Unknown",
            55,
        ))];
        let stats =
            apply_ml_suggestions(&mut new_directives, &existing, &default_fallbacks()).unwrap();
        assert_eq!(stats.inspected, 1);
        assert_eq!(stats.modified, 1);
        let Directive::Transaction(t) = &new_directives[0] else {
            panic!()
        };
        assert_eq!(t.postings[1].account.as_str(), "Expenses:Groceries");
    }

    #[test]
    fn skips_non_fallback_accounts() {
        let existing = training_set();
        let mut new_directives = vec![Directive::Transaction(txn(
            "Whole Foods",
            "Groceries",
            "Expenses:Groceries", // already categorized; should not touch
            55,
        ))];
        let stats =
            apply_ml_suggestions(&mut new_directives, &existing, &default_fallbacks()).unwrap();
        assert_eq!(stats.inspected, 0);
        assert_eq!(stats.modified, 0);
        let Directive::Transaction(t) = &new_directives[0] else {
            panic!()
        };
        assert_eq!(t.postings[1].account.as_str(), "Expenses:Groceries");
    }

    #[test]
    fn insufficient_training_data_is_noop() {
        // One existing txn isn't enough; should warn and return 0/0, not error.
        let existing = vec![txn("Store", "Stuff", "Expenses:Misc", 10)];
        let mut new_directives = vec![Directive::Transaction(txn(
            "Whole Foods",
            "Groceries",
            "Expenses:Unknown",
            55,
        ))];
        let stats =
            apply_ml_suggestions(&mut new_directives, &existing, &default_fallbacks()).unwrap();
        assert_eq!(stats.modified, 0);
        // Untouched.
        let Directive::Transaction(t) = &new_directives[0] else {
            panic!()
        };
        assert_eq!(t.postings[1].account.as_str(), "Expenses:Unknown");
    }

    #[test]
    fn honors_custom_fallback() {
        // A user configured `default_expense = "Expenses:Uncategorized"`.
        // ML should re-categorize that account, not the hardcoded default.
        let existing = training_set();
        let mut new_directives = vec![Directive::Transaction(txn(
            "Whole Foods",
            "Groceries",
            "Expenses:Uncategorized",
            55,
        ))];
        let custom = vec!["Expenses:Uncategorized".to_string()];
        let stats = apply_ml_suggestions(&mut new_directives, &existing, &custom).unwrap();
        assert_eq!(stats.inspected, 1);
        assert_eq!(stats.modified, 1);
        let Directive::Transaction(t) = &new_directives[0] else {
            panic!()
        };
        assert_eq!(t.postings[1].account.as_str(), "Expenses:Groceries");
    }
}
