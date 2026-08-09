//! Hover information support for the editor.

use rustledger_core::Directive;
use rustledger_parser::ParseResult;

use crate::types::EditorHoverInfo;

use super::helpers::{
    count_account_usages, count_currency_usages, get_word_at_position, is_currency_like,
};
use super::line_index::EditorCache;

/// Get hover information at the given position (using cached data).
pub fn get_hover_info_cached(
    source: &str,
    line: u32,
    character: u32,
    parse_result: &ParseResult,
    _cache: &EditorCache,
) -> Option<EditorHoverInfo> {
    // Hover doesn't benefit much from caching, but we keep the API consistent
    get_hover_info(source, line, character, parse_result)
}

/// Get hover information at the given position.
pub fn get_hover_info(
    source: &str,
    line: u32,
    character: u32,
    parse_result: &ParseResult,
) -> Option<EditorHoverInfo> {
    let word = get_word_at_position(source, line, character)?;

    // Check if it's an account name
    if (word.contains(':') || rustledger_core::is_default_account_root(&word))
        && let Some(info) = get_account_hover_info(&word, parse_result)
    {
        return Some(EditorHoverInfo {
            contents: info,
            range: None,
        });
    }

    // Check if it's a currency
    if is_currency_like(&word)
        && let Some(info) = get_currency_hover_info(&word, parse_result)
    {
        return Some(EditorHoverInfo {
            contents: info,
            range: None,
        });
    }

    // Check if it's a directive keyword
    if let Some(info) = get_directive_hover_info(&word) {
        return Some(EditorHoverInfo {
            contents: info,
            range: None,
        });
    }

    None
}

/// Get hover information about an account.
fn get_account_hover_info(account: &str, parse_result: &ParseResult) -> Option<String> {
    for spanned_directive in &parse_result.directives {
        if let Directive::Open(open) = &spanned_directive.value {
            let open_account = open.account.to_string();
            if open_account == account || account.starts_with(&format!("{open_account}:")) {
                let mut info = format!("## Account: `{open_account}`\n\n");
                let date = open.date;
                info.push_str(&format!("**Opened:** {date}\n\n"));

                if !open.currencies.is_empty() {
                    let currencies: Vec<String> = open
                        .currencies
                        .iter()
                        .map(std::string::ToString::to_string)
                        .collect();
                    let joined = currencies.join(", ");
                    info.push_str(&format!("**Currencies:** {joined}\n\n"));
                }

                let usage_count = count_account_usages(account, parse_result);
                info.push_str(&format!("**Used in:** {usage_count} postings"));

                return Some(info);
            }
        }
    }

    // Account not found in open directives
    let usage_count = count_account_usages(account, parse_result);
    if usage_count > 0 {
        return Some(format!(
            "## Account: `{account}`\n\n**Note:** No `open` directive found\n\n**Used in:** {usage_count} postings"
        ));
    }

    None
}

/// Get hover information about a currency.
fn get_currency_hover_info(currency: &str, parse_result: &ParseResult) -> Option<String> {
    for spanned_directive in &parse_result.directives {
        if let Directive::Commodity(comm) = &spanned_directive.value
            && comm.currency.as_ref() == currency
        {
            let mut info = format!("## Currency: `{currency}`\n\n");
            let date = comm.date;
            info.push_str(&format!("**Defined:** {date}\n"));

            let usage_count = count_currency_usages(currency, parse_result);
            info.push_str(&format!("\n**Used in:** {usage_count} amounts"));

            return Some(info);
        }
    }

    let usage_count = count_currency_usages(currency, parse_result);
    if usage_count > 0 {
        return Some(format!(
            "## Currency: `{currency}`\n\n**Note:** No `commodity` directive found\n\n**Used in:** {usage_count} amounts"
        ));
    }

    None
}

/// Get hover information about a directive keyword.
pub fn get_directive_hover_info(keyword: &str) -> Option<String> {
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
    use rustledger_parser::parse;

    #[test]
    fn test_get_hover_info_directive() {
        let source = "2024-01-01 open Assets:Bank USD";
        let result = parse(source);
        let hover = get_hover_info(source, 0, 11, &result);
        assert!(hover.is_some());
        assert!(hover.unwrap().contents.contains("open"));
    }

    #[test]
    fn test_get_hover_info_account() {
        let source = r#"2024-01-01 open Assets:Bank USD

2024-01-15 * "Coffee"
  Assets:Bank  -5.00 USD
  Expenses:Food
"#;
        let result = parse(source);
        let hover = get_hover_info(source, 0, 20, &result);
        assert!(hover.is_some());
        let contents = hover.unwrap().contents;
        assert!(contents.contains("Account"));
        assert!(contents.contains("Assets:Bank"));
    }

    #[test]
    fn test_get_hover_info_currency() {
        let source = "2024-01-01 commodity USD";
        let result = parse(source);
        let hover = get_hover_info(source, 0, 21, &result);
        assert!(hover.is_some());
        let contents = hover.unwrap().contents;
        assert!(contents.contains("Currency"));
        assert!(contents.contains("USD"));
    }

    #[test]
    fn test_get_hover_info_all_directives() {
        // Test a subset of directives with their expected content
        let tests = [
            ("open", "open"),
            ("close", "close"),
            ("commodity", "commodity"),
            ("balance", "balance"),
            ("pad", "pad"),
            ("event", "event"),
            ("note", "note"),
            ("document", "document"),
            ("query", "query"),
            ("custom", "custom"),
            ("price", "price"),
            ("*", "Transaction"),
            ("!", "Transaction"),
        ];

        for (keyword, expected_content) in tests {
            let info = get_directive_hover_info(keyword);
            assert!(info.is_some(), "should have hover for {keyword}");
            let content = info.as_ref().unwrap().to_lowercase();
            assert!(
                content.contains(&expected_content.to_lowercase()),
                "{keyword} hover should contain '{expected_content}', got: {}",
                info.unwrap()
            );
        }
    }
}
