//! Completion resolve handler for lazy-loading completion details.
//!
//! Provides additional information when a completion item is selected:
//! - Account completions: show current balance and transaction count
//! - Currency completions: show price history
//! - Payee completions: show recent transactions

use lsp_types::{CompletionItem, Documentation, MarkupContent, MarkupKind};
use rustledger_core::Decimal;
use rustledger_core::Directive;
use rustledger_parser::ParseResult;
use std::collections::HashMap;

use super::utils::{is_account_like, is_currency_like_simple};

/// Handle a completion item resolve request.
/// This adds detailed documentation to completion items.
pub fn handle_completion_resolve(
    item: CompletionItem,
    parse_result: &ParseResult,
) -> CompletionItem {
    let mut resolved = item.clone();

    // Check what kind of completion this is based on data field
    if let Some(data) = &item.data
        && let Some(kind) = data.get("kind").and_then(|v| v.as_str())
    {
        match kind {
            "account" => {
                if let Some(account) = data.get("account").and_then(|v| v.as_str()) {
                    resolved.documentation =
                        Some(resolve_account_documentation(account, parse_result));
                }
            }
            "currency" => {
                if let Some(currency) = data.get("currency").and_then(|v| v.as_str()) {
                    resolved.documentation =
                        Some(resolve_currency_documentation(currency, parse_result));
                }
            }
            "payee" => {
                if let Some(payee) = data.get("payee").and_then(|v| v.as_str()) {
                    resolved.documentation = Some(resolve_payee_documentation(payee, parse_result));
                }
            }
            _ => {}
        }
    }

    // If no data, try to infer from the label
    if resolved.documentation.is_none() {
        let label = &item.label;

        // Check if it looks like an account
        if is_account_like(label) {
            resolved.documentation = Some(resolve_account_documentation(label, parse_result));
        }
        // Check if it looks like a currency (all caps, 3-4 chars)
        else if is_currency_like_simple(label) {
            resolved.documentation = Some(resolve_currency_documentation(label, parse_result));
        }
    }

    resolved
}

/// Resolve documentation for an account completion.
fn resolve_account_documentation(account: &str, parse_result: &ParseResult) -> Documentation {
    let mut balances: HashMap<String, Decimal> = HashMap::new();
    let mut transaction_count = 0;
    let mut first_date: Option<chrono::NaiveDate> = None;
    let mut last_date: Option<chrono::NaiveDate> = None;

    for spanned in &parse_result.directives {
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
fn resolve_currency_documentation(currency: &str, parse_result: &ParseResult) -> Documentation {
    let mut prices: Vec<(chrono::NaiveDate, Decimal, String)> = Vec::new();
    let mut usage_count = 0;

    for spanned in &parse_result.directives {
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

/// Resolve documentation for a payee completion.
fn resolve_payee_documentation(payee: &str, parse_result: &ParseResult) -> Documentation {
    let mut transactions: Vec<(chrono::NaiveDate, String)> = Vec::new();
    let mut accounts_used: HashMap<String, usize> = HashMap::new();

    for spanned in &parse_result.directives {
        if let Directive::Transaction(txn) = &spanned.value
            && txn.payee.as_ref().map(|p| p.as_ref()) == Some(payee)
        {
            let narration = txn.narration.to_string();
            transactions.push((txn.date, narration));

            for posting in &txn.postings {
                *accounts_used
                    .entry(posting.account.to_string())
                    .or_default() += 1;
            }
        }
    }

    let mut doc = format!("**{}**\n\n", payee);

    doc.push_str(&format!("📊 **{} transactions**\n\n", transactions.len()));

    if !transactions.is_empty() {
        // Sort by date descending
        transactions.sort_by_key(|b| std::cmp::Reverse(b.0));

        doc.push_str("**Recent:**\n");
        for (date, narration) in transactions.iter().take(3) {
            let short_narration = if narration.len() > 30 {
                format!("{}...", &narration[..27])
            } else {
                narration.clone()
            };
            doc.push_str(&format!("- {} \"{}\"\n", date, short_narration));
        }

        if transactions.len() > 3 {
            doc.push_str(&format!("- _...and {} more_\n", transactions.len() - 3));
        }
    }

    if !accounts_used.is_empty() {
        doc.push_str("\n**Common accounts:**\n");
        let mut sorted: Vec<_> = accounts_used.into_iter().collect();
        sorted.sort_by_key(|b| std::cmp::Reverse(b.1));

        for (account, count) in sorted.iter().take(3) {
            doc.push_str(&format!("- {} ({}x)\n", account, count));
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

        let resolved = handle_completion_resolve(item, &result);
        assert!(resolved.documentation.is_some());

        if let Some(Documentation::MarkupContent(content)) = resolved.documentation {
            assert!(content.value.contains("Assets:Bank"));
            assert!(content.value.contains("2 transactions"));
            assert!(content.value.contains("95")); // 100 - 5
        }
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

        let resolved = handle_completion_resolve(item, &result);
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
