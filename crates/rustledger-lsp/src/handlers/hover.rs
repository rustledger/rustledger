//! Hover handler for displaying information about symbols.
//!
//! Provides hover information for:
//! - Accounts: open date, currencies, metadata
//! - Currencies: commodity directive info
//! - Transactions: posting summary

use lsp_types::{Hover, HoverContents, HoverParams, MarkupContent, MarkupKind};
use rustledger_core::Directive;
use rustledger_parser::{ParseResult, Spanned};

use crate::ledger_state::LedgerState;

use super::utils::{
    PositionEncoding, commodity_declaration_spans, get_word_at_source_position, is_account_type,
    is_currency_like_simple,
};

/// Handle a hover request.
pub fn handle_hover(
    params: &HoverParams,
    source: &str,
    parse_result: &ParseResult,
    ledger_state: Option<&LedgerState>,
    encoding: PositionEncoding,
) -> Option<Hover> {
    let position = params.text_document_position_params.position;

    // Get the word at the cursor position
    let word = get_word_at_source_position(source, position, encoding)?;

    tracing::debug!("Hover for word: {:?}", word);

    // Cross-file directives (from the loaded ledger) so an account opened in an
    // `include`d file still resolves on hover.
    let ledger_directives = ledger_state.and_then(LedgerState::directives);

    // Check if it's an account name
    if (word.contains(':') || is_account_type(&word))
        && let Some(info) = get_account_info(&word, parse_result, ledger_directives)
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
///
/// The `open` directive is looked up in the current file first, then in the
/// cross-file `ledger_directives` (the loaded ledger) so an account opened in
/// an `include`d file still shows its open date/currencies instead of a
/// spurious "No `open` directive found".
fn get_account_info(
    account: &str,
    parse_result: &ParseResult,
    ledger_directives: Option<&[Spanned<Directive>]>,
) -> Option<String> {
    let matches_open = |open: &rustledger_core::Open| {
        let oa = open.account.as_ref();
        account == oa
            || account
                .strip_prefix(oa)
                .is_some_and(|rest| rest.starts_with(':'))
    };
    let find_open = |dirs: &[Spanned<Directive>]| {
        dirs.iter().find_map(|sd| match &sd.value {
            Directive::Open(open) if matches_open(open) => Some(open.clone()),
            _ => None,
        })
    };

    let open =
        find_open(&parse_result.directives).or_else(|| ledger_directives.and_then(find_open));
    let usage_count = count_account_usages(account, parse_result);

    if let Some(open) = open {
        let mut info = format!("## Account: `{}`\n\n", open.account);
        info.push_str(&format!("**Opened:** {}\n\n", open.date));
        if !open.currencies.is_empty() {
            let currencies: Vec<String> = open.currencies.iter().map(|c| c.to_string()).collect();
            info.push_str(&format!("**Currencies:** {}\n\n", currencies.join(", ")));
        }
        info.push_str(&format!("**Used in:** {usage_count} postings"));
        return Some(info);
    }

    // No open found anywhere, but still provide usage info if it's referenced.
    if usage_count > 0 {
        return Some(format!(
            "## Account: `{account}`\n\n**Note:** No `open` directive found\n\n**Used in:** {usage_count} postings"
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
/// Count how many times `currency` is used (excluding its own
/// `Commodity` declaration). Consults the parser's
/// `currency_occurrences` index, so the count is exhaustive across
/// every position that produces a `Currency` token — `Amount`
/// (Transaction.units, Balance.amount, Price.amount, etc.),
/// `CostSpec.currency`, `PriceAnnotation.amount.currency`,
/// `Open.currencies` constraint lists, and `Currency`/`Amount`
/// metadata values. The previous implementation walked only
/// `Transaction.posting.units` and `Balance.amount`, silently
/// undercounting every other position.
fn count_currency_usages(currency: &str, parse_result: &ParseResult) -> usize {
    let declaration_spans = commodity_declaration_spans(parse_result);
    parse_result
        .currency_occurrences
        .iter()
        .filter(|o| o.value == currency && !declaration_spans.contains(&o.span))
        .count()
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
    use rustledger_parser::parse;

    #[test]
    fn test_get_account_info_resolves_included_open() {
        // Current file uses the account but does not open it.
        let pr = parse("2024-02-01 * \"x\"\n  Assets:Shared 1 USD\n  Assets:Shared -1 USD\n");
        // The `open` lives in an included file, supplied via ledger_directives.
        let inc = parse("2024-01-01 open Assets:Shared USD\n");

        // Single-file only: spurious "No open directive found".
        let single = get_account_info("Assets:Shared", &pr, None).expect("usage info");
        assert!(single.contains("No `open` directive found"));

        // With cross-file directives: resolves the open from the include.
        let cross =
            get_account_info("Assets:Shared", &pr, Some(&inc.directives)).expect("account info");
        assert!(cross.contains("**Opened:** 2024-01-01"), "got: {cross}");
        assert!(
            !cross.contains("No `open`"),
            "should not claim missing open: {cross}"
        );
    }

    #[test]
    fn test_get_directive_info() {
        assert!(get_directive_info("open").is_some());
        assert!(get_directive_info("close").is_some());
        assert!(get_directive_info("*").is_some());
        assert!(get_directive_info("unknown").is_none());
    }

    /// Regression test for the previous undercounting bug in
    /// `count_currency_usages`. The old implementation only walked
    /// `Transaction.posting.units` and `Balance.amount`, so it
    /// silently missed every other position that can carry a
    /// currency. This test exercises a transaction whose currency
    /// only appears in a `CostSpec`, plus an `Open.currencies`
    /// constraint list — both positions the old walk missed.
    #[test]
    fn test_count_currency_usages_exhaustive() {
        use rustledger_parser::parse;

        // USD appears in: Commodity declaration (excluded);
        // Open.currencies; Balance.amount; Posting.units;
        // CostSpec.currency; Price directive (currency + amount.currency).
        let source = r#"2024-01-01 commodity USD
2024-01-01 open Assets:Bank USD
2024-01-15 * "Buy stock"
  Assets:Stock  10 AAPL {150 USD}
  Assets:Bank
2024-01-20 balance Assets:Bank -1500 USD
2024-01-21 price AAPL  155 USD
"#;
        let parse_result = parse(source);
        assert!(
            parse_result.errors.is_empty(),
            "parse errors: {:?}",
            parse_result.errors
        );

        let count = count_currency_usages("USD", &parse_result);

        // Hand-counted uses (excluding the Commodity declaration):
        //   1. Open.currencies USD
        //   2. CostSpec {150 USD}
        //   3. Balance amount USD
        //   4. Price amount USD (the quote currency in `155 USD`)
        //
        // (The Price directive's *base* currency is `AAPL`, not
        // USD, so it doesn't contribute.)
        //
        // The pre-fix walk would have returned 1 (just the
        // Balance — Transaction.posting.units.currency() returns
        // the units side, not the cost side, and the missing
        // `Assets:Bank` posting has no units).
        assert_eq!(
            count, 4,
            "expected 4 USD usages (Open + CostSpec + Balance + Price.amount); got {count}"
        );
    }
}
