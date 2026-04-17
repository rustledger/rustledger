//! Hover handler for displaying information about symbols.
//!
//! Provides hover information for:
//! - Accounts: open date, currencies, metadata
//! - Currencies: commodity directive info
//! - Transactions: posting summary

use lsp_types::{Hover, HoverContents, HoverParams, MarkupContent, MarkupKind};
use rustledger_core::Directive;
use rustledger_parser::ParseResult;

use super::utils::{get_word_at_source_position, is_account_type, is_currency_like_simple};

/// Handle a hover request.
pub fn handle_hover(
    params: &HoverParams,
    source: &str,
    parse_result: &ParseResult,
) -> Option<Hover> {
    let position = params.text_document_position_params.position;

    // Get the word at the cursor position
    let word = get_word_at_source_position(source, position)?;

    tracing::debug!("Hover for word: {:?}", word);

    // Check if it's an account name
    if (word.contains(':') || is_account_type(&word))
        && let Some(info) = get_account_info(&word, parse_result)
    {
        return Some(Hover {
            contents: HoverContents::Markup(MarkupContent {
                kind: MarkupKind::Markdown,
                value: info,
            }),
            range: None,
        });
    }

    // Check if it's a currency
    if is_currency_like_simple(&word)
        && let Some(info) = get_currency_info(&word, parse_result)
    {
        return Some(Hover {
            contents: HoverContents::Markup(MarkupContent {
                kind: MarkupKind::Markdown,
                value: info,
            }),
            range: None,
        });
    }

    // Check if it's a directive keyword
    if let Some(info) = get_directive_info(&word) {
        return Some(Hover {
            contents: HoverContents::Markup(MarkupContent {
                kind: MarkupKind::Markdown,
                value: info,
            }),
            range: None,
        });
    }

    None
}

/// Get information about an account.
fn get_account_info(account: &str, parse_result: &ParseResult) -> Option<String> {
    // Find the open directive for this account
    for spanned_directive in &parse_result.directives {
        if let Directive::Open(open) = &spanned_directive.value {
            let open_account = open.account.to_string();
            if open_account == account || account.starts_with(&format!("{}:", open_account)) {
                let mut info = format!("## Account: `{}`\n\n", open_account);

                // Add open date
                info.push_str(&format!("**Opened:** {}\n\n", open.date));

                // Add currencies if any
                if !open.currencies.is_empty() {
                    let currencies: Vec<String> =
                        open.currencies.iter().map(|c| c.to_string()).collect();
                    info.push_str(&format!("**Currencies:** {}\n\n", currencies.join(", ")));
                }

                // Count usages
                let usage_count = count_account_usages(account, parse_result);
                info.push_str(&format!("**Used in:** {} postings", usage_count));

                return Some(info);
            }
        }
    }

    // Account not found in open directives, but still provide usage info
    let usage_count = count_account_usages(account, parse_result);
    if usage_count > 0 {
        return Some(format!(
            "## Account: `{}`\n\n**Note:** No `open` directive found\n\n**Used in:** {} postings",
            account, usage_count
        ));
    }

    None
}

/// Count how many times an account is used in postings.
fn count_account_usages(account: &str, parse_result: &ParseResult) -> usize {
    let mut count = 0;
    for spanned_directive in &parse_result.directives {
        if let Directive::Transaction(txn) = &spanned_directive.value {
            for posting in &txn.postings {
                if posting.account.as_ref() == account {
                    count += 1;
                }
            }
        }
    }
    count
}

/// Get information about a currency.
fn get_currency_info(currency: &str, parse_result: &ParseResult) -> Option<String> {
    // Find the commodity directive for this currency
    for spanned_directive in &parse_result.directives {
        if let Directive::Commodity(comm) = &spanned_directive.value
            && comm.currency.as_ref() == currency
        {
            let mut info = format!("## Currency: `{}`\n\n", currency);
            info.push_str(&format!("**Defined:** {}\n", comm.date));

            // Count usages
            let usage_count = count_currency_usages(currency, parse_result);
            info.push_str(&format!("\n**Used in:** {} amounts", usage_count));

            return Some(info);
        }
    }

    // Currency not found in commodity directives, but still provide usage info
    let usage_count = count_currency_usages(currency, parse_result);
    if usage_count > 0 {
        return Some(format!(
            "## Currency: `{}`\n\n**Note:** No `commodity` directive found\n\n**Used in:** {} amounts",
            currency, usage_count
        ));
    }

    None
}

/// Count how many times a currency is used.
#[allow(clippy::cmp_owned)]
fn count_currency_usages(currency: &str, parse_result: &ParseResult) -> usize {
    let mut count = 0;
    for spanned_directive in &parse_result.directives {
        match &spanned_directive.value {
            Directive::Transaction(txn) => {
                for posting in &txn.postings {
                    if let Some(ref units) = posting.units
                        && let Some(c) = units.currency()
                        && c.to_string() == currency
                    {
                        count += 1;
                    }
                }
            }
            Directive::Balance(bal) if bal.amount.currency.as_ref() == currency => {
                count += 1;
            }
            _ => {}
        }
    }
    count
}

/// Get information about a directive keyword.
fn get_directive_info(keyword: &str) -> Option<String> {
    let info = match keyword {
        "open" => {
            "## `open` Directive\n\nOpens an account for use in transactions.\n\n```beancount\n2024-01-01 open Assets:Bank USD\n```"
        }
        "close" => {
            "## `close` Directive\n\nCloses an account. No transactions allowed after this date.\n\n```beancount\n2024-12-31 close Assets:OldBank\n```"
        }
        "commodity" => {
            "## `commodity` Directive\n\nDefines a currency or commodity.\n\n```beancount\n2024-01-01 commodity USD\n```"
        }
        "balance" => {
            "## `balance` Directive\n\nAsserts the balance of an account at a given date.\n\n```beancount\n2024-01-01 balance Assets:Bank 1000.00 USD\n```"
        }
        "pad" => {
            "## `pad` Directive\n\nAutomatically pads an account to match a balance assertion.\n\n```beancount\n2024-01-01 pad Assets:Bank Equity:Opening-Balances\n```"
        }
        "event" => {
            "## `event` Directive\n\nRecords a named event with a value.\n\n```beancount\n2024-01-01 event \"location\" \"New York\"\n```"
        }
        "note" => {
            "## `note` Directive\n\nAttaches a note to an account.\n\n```beancount\n2024-01-01 note Assets:Bank \"Account opened\"\n```"
        }
        "document" => {
            "## `document` Directive\n\nLinks a document to an account.\n\n```beancount\n2024-01-01 document Assets:Bank \"/path/to/statement.pdf\"\n```"
        }
        "query" => {
            "## `query` Directive\n\nDefines a named BQL query.\n\n```beancount\n2024-01-01 query \"expenses\" \"SELECT account, sum(amount)\"\n```"
        }
        "custom" => {
            "## `custom` Directive\n\nA custom directive for extensions.\n\n```beancount\n2024-01-01 custom \"budget\" Expenses:Food 500.00 USD\n```"
        }
        "price" => {
            "## `price` Directive\n\nRecords a price for a commodity.\n\n```beancount\n2024-01-01 price BTC 45000.00 USD\n```"
        }
        "txn" | "*" => {
            "## Transaction\n\nA complete (balanced) transaction.\n\n```beancount\n2024-01-01 * \"Payee\" \"Description\"\n  Assets:Bank  -100.00 USD\n  Expenses:Food\n```"
        }
        "!" => {
            "## Transaction (Incomplete)\n\nAn incomplete or flagged transaction.\n\n```beancount\n2024-01-01 ! \"Payee\" \"Needs review\"\n  Assets:Bank  -100.00 USD\n  Expenses:Unknown\n```"
        }
        "include" => {
            "## `include` Directive\n\nIncludes another Beancount file.\n\n```beancount\ninclude \"other-file.beancount\"\n```"
        }
        "option" => {
            "## `option` Directive\n\nSets a Beancount option.\n\n```beancount\noption \"operating_currency\" \"USD\"\n```"
        }
        "plugin" => {
            "## `plugin` Directive\n\nLoads a plugin.\n\n```beancount\nplugin \"beancount.plugins.auto_accounts\"\n```"
        }
        _ => return None,
    };

    Some(info.to_string())
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_get_directive_info() {
        assert!(get_directive_info("open").is_some());
        assert!(get_directive_info("close").is_some());
        assert!(get_directive_info("*").is_some());
        assert!(get_directive_info("unknown").is_none());
    }

    // Tests for shared utilities removed - they are tested in utils module
}
