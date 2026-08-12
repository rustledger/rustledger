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
    PositionEncoding, commodity_declaration_spans, count_noun, get_word_at_source_position,
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
    if (word.contains(':') || rustledger_core::is_default_account_root(&word))
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
/// The `open` directive is looked up across the current file and the cross-file
/// `ledger_directives` (the loaded ledger), so an account opened in an
/// `include`d file still shows its open date/currencies instead of a spurious
/// "No `open` directive found".
///
/// Several `open`s can describe the hovered account at once — a ledger may open
/// a catch-all `Expenses:Food` as well as `Expenses:Food:Restaurant` — so the
/// MOST SPECIFIC one is chosen rather than the first encountered. An exact
/// `open` is the longest possible match and therefore always wins, whatever
/// order the directives happen to appear in. Selecting positionally meant a
/// parent declared before its child hijacked the child's popup, which is the
/// norm in any alphabetically sorted account list (#2021).
fn get_account_info(
    account: &str,
    parse_result: &ParseResult,
    ledger_directives: Option<&[Spanned<Directive>]>,
) -> Option<String> {
    let describes_account = |open: &rustledger_core::Open| {
        let oa = open.account.as_ref();
        account == oa
            || account
                .strip_prefix(oa)
                .is_some_and(|rest| rest.starts_with(':'))
    };

    // Rank the two sources explicitly and sort on `(specificity, source)`
    // rather than leaning on `max_by_key`'s last-maximum-wins tie behavior.
    // The tie is reachable and the choice matters: `LedgerState::directives`
    // is the whole loaded ledger, which includes THIS file as loaded from
    // disk, so when the same account is opened in both the buffer copy is the
    // live one and the ledger copy may be stale by an unsaved edit.
    const FROM_LEDGER: u8 = 0;
    const FROM_BUFFER: u8 = 1;
    let open = ledger_directives
        .into_iter()
        .map(|dirs| (FROM_LEDGER, dirs))
        .chain(std::iter::once((
            FROM_BUFFER,
            parse_result.directives.as_slice(),
        )))
        .flat_map(|(source, dirs)| dirs.iter().map(move |sd| (source, sd)))
        .filter_map(|(source, sd)| match &sd.value {
            Directive::Open(open) if describes_account(open) => Some((source, open)),
            _ => None,
        })
        .max_by_key(|(source, open)| (open.account.as_ref().len(), *source))
        .map(|(_, open)| open.clone());
    let usage_count = count_account_usages(account, parse_result);

    if let Some(open) = open {
        // Always title with the account under the cursor. Titling with
        // `open.account` was the visible half of #2021: an ancestor's name was
        // presented as though it were the hovered account.
        let mut info = format!("## Account: `{account}`\n\n");
        let currencies: Vec<String> = open.currencies.iter().map(|c| c.to_string()).collect();
        if open.account.as_ref() == account {
            info.push_str(&format!("**Opened:** {}\n\n", open.date));
            if !currencies.is_empty() {
                info.push_str(&format!("**Currencies:** {}\n\n", currencies.join(", ")));
            }
        } else {
            // Only an ancestor is declared. Attribute its date and currency
            // constraint to it by name instead of letting them read as this
            // account's own — and say so explicitly, so a missing
            // `**Currencies:**` line is explained rather than just absent.
            info.push_str(&format!(
                "**Note:** no `open` for this account; nearest declared ancestor is `{}` (opened {})\n\n",
                open.account, open.date
            ));
            if !currencies.is_empty() {
                info.push_str(&format!(
                    "**Currencies (from `{}`):** {}\n\n",
                    open.account,
                    currencies.join(", ")
                ));
            }
        }
        info.push_str(&format!(
            "**Used in:** {}",
            count_noun(usage_count, "posting")
        ));
        return Some(info);
    }

    // No open found anywhere, but still provide usage info if it's referenced.
    if usage_count > 0 {
        return Some(format!(
            "## Account: `{account}`\n\n**Note:** No `open` directive found\n\n**Used in:** {}",
            count_noun(usage_count, "posting")
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
            info.push_str(&format!(
                "\n**Used in:** {}",
                count_noun(usage_count, "amount")
            ));

            return Some(info);
        }
    }

    // Currency not found in commodity directives, but still provide usage info
    let usage_count = count_currency_usages(currency, parse_result);
    if usage_count > 0 {
        return Some(format!(
            "## Currency: `{}`\n\n**Note:** No `commodity` directive found\n\n**Used in:** {}",
            currency,
            count_noun(usage_count, "amount")
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

    /// #2021: an exact `open` must win over an ancestor's, whichever is
    /// declared first. The issue's own repro, run in both directive orders —
    /// identical content, so both must produce identical hover text.
    #[test]
    fn test_account_info_prefers_exact_open_over_ancestor() {
        let parent_first = parse(concat!(
            "2014-01-01 open Assets:Bank\n",
            "2014-01-01 open Assets:Bank:Checking USD\n",
        ));
        let child_first = parse(concat!(
            "2014-01-01 open Assets:Bank:Checking USD\n",
            "2014-01-01 open Assets:Bank\n",
        ));

        for (name, pr) in [
            ("parent_first", &parent_first),
            ("child_first", &child_first),
        ] {
            assert!(pr.errors.is_empty(), "{name} must parse: {:?}", pr.errors);
        }
        let a = get_account_info("Assets:Bank:Checking", &parent_first, None).expect("info");
        let b = get_account_info("Assets:Bank:Checking", &child_first, None).expect("info");

        assert_eq!(
            a, b,
            "declaration order must not change the hover text\n{a}\n---\n{b}"
        );
        // Pre-fix, `parent_first` produced "## Account: `Assets:Bank`" with no
        // currencies — the ancestor's `open`, wearing the child's name.
        assert!(a.contains("## Account: `Assets:Bank:Checking`"), "got: {a}");
        assert!(a.contains("**Currencies:** USD"), "got: {a}");
        assert!(
            !a.contains("nearest declared ancestor"),
            "an exact open is not an ancestor fallback: {a}"
        );
    }

    /// The catch-all-parent shape from the issue, which is the norm in an
    /// alphabetically sorted account list.
    #[test]
    fn test_account_info_exact_open_wins_for_sorted_catch_all_parent() {
        let pr = parse(concat!(
            "2020-01-01 open Expenses:Food USD\n",
            "2020-01-01 open Expenses:Food:Restaurant USD\n",
        ));
        assert!(pr.errors.is_empty(), "fixture must parse: {:?}", pr.errors);
        let info = get_account_info("Expenses:Food:Restaurant", &pr, None).expect("info");
        assert!(
            info.contains("## Account: `Expenses:Food:Restaurant`"),
            "got: {info}"
        );
        // The title alone is not enough — it is now always the hovered
        // account, so it stays right even if the WRONG open were selected.
        // These pin the selection itself.
        assert!(
            !info.contains("nearest declared ancestor"),
            "the exact open must be selected, not the catch-all parent: {info}"
        );
        assert!(info.contains("**Currencies:** USD"), "got: {info}");
    }

    /// With no exact `open`, the LONGEST ancestor is used — not the first —
    /// the popup is still titled with the hovered account, and the ancestor's
    /// facts are attributed to it rather than presented as this account's own.
    #[test]
    fn test_account_info_falls_back_to_longest_ancestor() {
        // Two real ancestors, shallowest first, so a positional search picks
        // `Assets:Bank`. (A single-segment `open Assets` does not parse, so it
        // cannot be used as the decoy candidate here.)
        let pr = parse(concat!(
            "2020-01-01 open Assets:Bank\n",
            "2020-01-01 open Assets:Bank:Checking EUR\n",
        ));
        assert!(pr.errors.is_empty(), "fixture must parse: {:?}", pr.errors);
        let info = get_account_info("Assets:Bank:Checking:Sub", &pr, None).expect("info");

        assert!(
            info.contains("## Account: `Assets:Bank:Checking:Sub`"),
            "titled with the hovered account: {info}"
        );
        assert!(
            info.contains("nearest declared ancestor is `Assets:Bank:Checking`"),
            "longest ancestor, and named as such: {info}"
        );
        assert!(
            info.contains("**Currencies (from `Assets:Bank:Checking`):** EUR"),
            "the constraint is attributed, not claimed: {info}"
        );
        assert!(
            !info.contains("**Opened:**"),
            "an ancestor's date is not this account's open date: {info}"
        );
    }

    /// An exact `open` in an included file still beats an ancestor declared in
    /// the file being edited — the selection is over both sources at once.
    #[test]
    fn test_account_info_exact_open_from_include_beats_local_ancestor() {
        let pr = parse("2014-01-01 open Assets:Bank\n");
        let inc = parse("2014-01-01 open Assets:Bank:Checking USD\n");
        let info = get_account_info("Assets:Bank:Checking", &pr, Some(&inc.directives))
            .expect("account info");
        assert!(
            info.contains("## Account: `Assets:Bank:Checking`"),
            "got: {info}"
        );
        assert!(info.contains("**Currencies:** USD"), "got: {info}");
    }

    /// On an EQUALLY specific match the buffer wins, not the loaded ledger.
    /// `LedgerState::directives` includes this file as loaded from disk, so the
    /// ledger's copy of the same `open` can be stale by an unsaved edit.
    #[test]
    fn test_account_info_prefers_buffer_over_stale_ledger_copy() {
        // The buffer holds the edit the user just made — a later date and a USD
        // constraint; the on-disk ledger still has the original line.
        let buffer = parse("2024-02-01 open Assets:Bank:Checking USD\n");
        let stale = parse("2014-01-01 open Assets:Bank:Checking\n");
        assert!(buffer.errors.is_empty(), "{:?}", buffer.errors);
        assert!(stale.errors.is_empty(), "{:?}", stale.errors);

        let info = get_account_info("Assets:Bank:Checking", &buffer, Some(&stale.directives))
            .expect("info");
        assert!(
            info.contains("**Opened:** 2024-02-01"),
            "the live buffer's open must win: {info}"
        );
        assert!(
            info.contains("**Currencies:** USD"),
            "the live buffer's constraint must win: {info}"
        );
    }

    /// A sibling sharing a name prefix is not an ancestor. `Assets:Bank` is a
    /// string prefix of `Assets:Banking` but not its parent, so hovering
    /// `Assets:Banking` must not pick it up.
    ///
    /// The direction matters: the check asks whether the OPEN prefixes the
    /// HOVERED account, so the decoy has to be the shorter of the two. An
    /// earlier version of this test had them the other way round, where
    /// `strip_prefix` returns `None` outright and the `:` boundary is never
    /// reached — it could not fail.
    #[test]
    fn test_account_info_ignores_prefix_sibling() {
        let pr = parse("2020-01-01 open Assets:Bank USD\n");
        // Pin the fixture. An `is_none()` assertion is satisfied just as well
        // by an `open` that failed to parse, so without this the test would go
        // vacuous the moment account-name validation changed — exactly what
        // made an earlier draft of the ancestor test above meaningless.
        assert!(pr.errors.is_empty(), "fixture must parse: {:?}", pr.errors);
        // Nothing describes `Assets:Banking` and it is used nowhere, so there
        // is nothing to report at all.
        let info = get_account_info("Assets:Banking", &pr, None);
        assert!(info.is_none(), "got: {info:?}");
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
