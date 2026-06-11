//! Completion resolve handler for lazy-loading completion details.
//!
//! Provides additional information when a completion item is selected:
//! - Account completions: show current balance and transaction count
//! - Currency completions: show price history

use lsp_types::{CompletionItem, Documentation, MarkupContent, MarkupKind};
use rustledger_core::Decimal;
use rustledger_core::Directive;
use rustledger_parser::Spanned;
use std::collections::HashMap;

use super::utils::{is_account_like, is_currency_like_simple};

/// Handle a completion item resolve request.
/// This adds detailed documentation to completion items.
///
/// `directives` is the set of directives to aggregate over. The caller
/// passes the *full ledger* (all `include`d files, resolved via the
/// `journalFile` setting) when one is configured, falling back to the
/// directives of the currently edited file otherwise. Resolving against
/// the full ledger keeps the detail popup (balances, transaction counts,
/// price history) consistent with `hover`, instead of reflecting only
/// the month/file the cursor happens to be in (issue #1297).
pub fn handle_completion_resolve(
    item: CompletionItem,
    directives: &[Spanned<Directive>],
) -> CompletionItem {
    let mut resolved = item.clone();

    // The detail is inferred from the label shape. `handle_completion`
    // attaches only `{uri}` to each item's `data` (never a structured
    // "kind"), so there is nothing else to dispatch on here: an
    // account-like label gets balance/transaction detail, a
    // currency-like label gets price history. Labels that match neither
    // (payees, tags, links) have no detail popup — resolving those
    // would require the producer to tag items with a kind, which it
    // does not currently do.
    //
    // Only fill documentation the item doesn't already carry: a resolve
    // handler adds missing detail, it doesn't clobber what a producer
    // (or a client round-trip) may have set eagerly.
    if resolved.documentation.is_none() {
        let label = &item.label;
        if is_account_like(label) {
            resolved.documentation = Some(resolve_account_documentation(label, directives));
        } else if is_currency_like_simple(label) {
            resolved.documentation = Some(resolve_currency_documentation(label, directives));
        }
    }

    resolved
}

/// Resolve documentation for an account completion.
fn resolve_account_documentation(
    account: &str,
    directives: &[Spanned<Directive>],
) -> Documentation {
    let mut balances: HashMap<String, Decimal> = HashMap::new();
    let mut transaction_count = 0;
    let mut first_date: Option<rustledger_core::NaiveDate> = None;
    let mut last_date: Option<rustledger_core::NaiveDate> = None;

    for spanned in directives {
        if let Directive::Transaction(txn) = &spanned.value {
            for posting in &txn.postings {
                if posting.account.as_ref() == account {
                    transaction_count += 1;

                    // Track dates
                    if first_date.is_none() || Some(txn.date) < first_date {
                        first_date = Some(txn.date);
                    }
                    if last_date.is_none() || Some(txn.date) > last_date {
                        last_date = Some(txn.date);
                    }

                    // Track balance
                    if let Some(units) = &posting.units
                        && let Some(number) = units.number()
                    {
                        let currency = units.currency().unwrap_or("???").to_string();
                        *balances.entry(currency).or_default() += number;
                    }
                }
            }
        }
    }

    let mut doc = format!("**{}**\n\n", account);

    if transaction_count > 0 {
        doc.push_str(&format!("📊 **{} transactions**\n\n", transaction_count));

        if let (Some(first), Some(last)) = (first_date, last_date) {
            doc.push_str(&format!("📅 {} → {}\n\n", first, last));
        }

        if !balances.is_empty() {
            doc.push_str("**Current Balance:**\n");
            for (currency, amount) in &balances {
                doc.push_str(&format!("- {} {}\n", amount, currency));
            }
        }
    } else {
        doc.push_str("_No transactions found_");
    }

    Documentation::MarkupContent(MarkupContent {
        kind: MarkupKind::Markdown,
        value: doc,
    })
}

/// Resolve documentation for a currency completion.
fn resolve_currency_documentation(
    currency: &str,
    directives: &[Spanned<Directive>],
) -> Documentation {
    let mut prices: Vec<(rustledger_core::NaiveDate, Decimal, String)> = Vec::new();
    let mut usage_count = 0;

    for spanned in directives {
        match &spanned.value {
            Directive::Price(price) if price.currency.as_ref() == currency => {
                prices.push((
                    price.date,
                    price.amount.number,
                    price.amount.currency.to_string(),
                ));
            }
            Directive::Transaction(txn) => {
                for posting in &txn.postings {
                    if let Some(units) = &posting.units
                        && units.currency() == Some(currency)
                    {
                        usage_count += 1;
                    }
                }
            }
            _ => {}
        }
    }

    let mut doc = format!("**{}**\n\n", currency);

    doc.push_str(&format!("📊 Used in **{} postings**\n\n", usage_count));

    if !prices.is_empty() {
        // Sort by date descending
        prices.sort_by_key(|b| std::cmp::Reverse(b.0));

        doc.push_str("**Recent Prices:**\n");
        for (date, amount, quote_currency) in prices.iter().take(5) {
            doc.push_str(&format!("- {}: {} {}\n", date, amount, quote_currency));
        }

        if prices.len() > 5 {
            doc.push_str(&format!("- _...and {} more_\n", prices.len() - 5));
        }
    }

    Documentation::MarkupContent(MarkupContent {
        kind: MarkupKind::Markdown,
        value: doc,
    })
}

#[cfg(test)]
mod tests {
    use super::super::utils::{is_account_like, is_currency_like_simple};
    use super::*;
    use rustledger_parser::parse;

    #[test]
    fn test_resolve_account_completion() {
        let source = r#"2024-01-01 open Assets:Bank USD
2024-01-15 * "Deposit"
  Assets:Bank  100.00 USD
  Income:Salary
2024-01-20 * "Coffee"
  Assets:Bank  -5.00 USD
  Expenses:Food
"#;
        let result = parse(source);

        let item = CompletionItem {
            label: "Assets:Bank".to_string(),
            ..Default::default()
        };

        let resolved = handle_completion_resolve(item, &result.directives);
        assert!(resolved.documentation.is_some());

        if let Some(Documentation::MarkupContent(content)) = resolved.documentation {
            assert!(content.value.contains("Assets:Bank"));
            assert!(content.value.contains("2 transactions"));
            assert!(content.value.contains("95")); // 100 - 5
        }
    }

    /// Regression for #1297: the resolve detail must aggregate over
    /// every directive it's handed, not just the current file. When a
    /// `journalFile` is configured the caller passes the full ledger's
    /// directives (all `include`d files merged), so a completion
    /// resolved while editing one monthly file still reports the
    /// whole-ledger balance and transaction count — matching `hover`.
    ///
    /// This simulates the multi-file case by concatenating the
    /// directives from two "files" (two parses) into one slice, the
    /// same shape `LedgerState::directives()` hands the call site.
    #[test]
    fn resolve_account_aggregates_across_full_ledger() {
        // "Current file" the cursor is in: only January's activity.
        let jan = parse(
            r#"2024-01-15 * "Deposit"
  Assets:Bank  100.00 USD
  Income:Salary
"#,
        );
        // Another included file: February's activity.
        let feb = parse(
            r#"2024-02-10 * "Coffee"
  Assets:Bank  -5.00 USD
  Expenses:Food
2024-02-20 * "Lunch"
  Assets:Bank  -10.00 USD
  Expenses:Food
"#,
        );

        // The full ledger = every file's directives merged. This is
        // what the resolve handler receives when journalFile is set.
        let mut full_ledger = jan.directives.clone();
        full_ledger.extend(feb.directives.iter().cloned());

        let item = CompletionItem {
            label: "Assets:Bank".to_string(),
            ..Default::default()
        };

        // Resolving against only the current file would report 1
        // transaction and a 100.00 balance. Against the full ledger it
        // must see all three postings.
        let resolved = handle_completion_resolve(item, &full_ledger);
        let Some(Documentation::MarkupContent(content)) = resolved.documentation else {
            panic!("expected markdown documentation");
        };
        assert!(
            content.value.contains("3 transactions"),
            "should count postings across all files; got:\n{}",
            content.value
        );
        assert!(
            content.value.contains("85"), // 100 - 5 - 10
            "balance should aggregate across all files; got:\n{}",
            content.value
        );
        // Date range should span both files (Jan → Feb).
        assert!(
            content.value.contains("2024-01-15") && content.value.contains("2024-02-20"),
            "date range should span the full ledger; got:\n{}",
            content.value
        );
    }

    #[test]
    fn test_resolve_currency_completion() {
        let source = r#"2024-01-01 price AAPL 150 USD
2024-01-15 price AAPL 155 USD
2024-01-15 * "Buy stock"
  Assets:Brokerage  10 AAPL
  Assets:Bank  -1500 USD
"#;
        let result = parse(source);

        let item = CompletionItem {
            label: "AAPL".to_string(),
            ..Default::default()
        };

        let resolved = handle_completion_resolve(item, &result.directives);
        assert!(resolved.documentation.is_some());

        if let Some(Documentation::MarkupContent(content)) = resolved.documentation {
            assert!(content.value.contains("AAPL"));
            assert!(content.value.contains("Recent Prices"));
        }
    }

    #[test]
    fn test_is_account_like() {
        assert!(is_account_like("Assets:Bank"));
        assert!(is_account_like("Expenses:Food:Coffee"));
        assert!(!is_account_like("USD"));
        assert!(!is_account_like("hello"));
    }

    #[test]
    fn test_is_currency_like() {
        assert!(is_currency_like_simple("USD"));
        assert!(is_currency_like_simple("AAPL"));
        assert!(is_currency_like_simple("BTC"));
        assert!(!is_currency_like_simple("Assets:Bank"));
        assert!(!is_currency_like_simple("hello world"));
    }
}
