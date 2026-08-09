//! Find references support for the editor.

use rustledger_core::Directive;
use rustledger_parser::ParseResult;

use crate::types::{EditorRange, EditorReference, EditorReferencesResult, ReferenceKind};

use super::helpers::{
    find_nth_word_in_line, find_quoted_string_in_line, find_word_in_line, get_line,
    get_word_at_position, is_currency_like,
};
use super::line_index::{EditorCache, LineIndex};

/// Find all references to the symbol at the given position (using cached data).
pub fn get_references_cached(
    source: &str,
    line: u32,
    character: u32,
    parse_result: &ParseResult,
    cache: &EditorCache,
) -> Option<EditorReferencesResult> {
    let word = get_word_at_position(source, line, character)?;

    // Check if it's an account name
    if word.contains(':') || rustledger_core::is_default_account_root(&word) {
        return Some(find_account_references(
            &word,
            source,
            parse_result,
            &cache.line_index,
        ));
    }

    // Check if it's a currency
    if is_currency_like(&word) && cache.currencies.contains(&word) {
        return Some(find_currency_references(
            &word,
            source,
            parse_result,
            &cache.line_index,
        ));
    }

    // Check if it's a payee (inside quotes on a transaction line)
    if cache.payees.contains(&word) {
        return Some(find_payee_references(
            &word,
            source,
            parse_result,
            &cache.line_index,
        ));
    }

    None
}

/// Find all references to an account.
fn find_account_references(
    account: &str,
    source: &str,
    parse_result: &ParseResult,
    line_index: &LineIndex,
) -> EditorReferencesResult {
    let mut references = Vec::new();

    for spanned_directive in &parse_result.directives {
        let (start_line, _) = line_index.offset_to_position(spanned_directive.span.start);
        let directive_line = get_line(source, start_line as usize);

        match &spanned_directive.value {
            Directive::Open(open) => {
                let open_account = open.account.to_string();
                if (open_account == account || account.starts_with(&format!("{open_account}:")))
                    && let Some(range) =
                        find_word_in_line(directive_line, &open_account, start_line)
                {
                    references.push(EditorReference {
                        range,
                        kind: ReferenceKind::Account,
                        is_definition: true,
                        context: Some("open".to_string()),
                    });
                }
            }
            Directive::Close(close) => {
                let close_account = close.account.to_string();
                if close_account == account
                    && let Some(range) =
                        find_word_in_line(directive_line, &close_account, start_line)
                {
                    references.push(EditorReference {
                        range,
                        kind: ReferenceKind::Account,
                        is_definition: false,
                        context: Some("close".to_string()),
                    });
                }
            }
            Directive::Balance(bal) => {
                let bal_account = bal.account.to_string();
                if bal_account == account
                    && let Some(range) = find_word_in_line(directive_line, &bal_account, start_line)
                {
                    references.push(EditorReference {
                        range,
                        kind: ReferenceKind::Account,
                        is_definition: false,
                        context: Some("balance".to_string()),
                    });
                }
            }
            Directive::Pad(pad) => {
                let pad_account = pad.account.to_string();
                let source_account = pad.source_account.to_string();
                if pad_account == account
                    && let Some(range) = find_word_in_line(directive_line, &pad_account, start_line)
                {
                    references.push(EditorReference {
                        range,
                        kind: ReferenceKind::Account,
                        is_definition: false,
                        context: Some("pad".to_string()),
                    });
                }
                if source_account == account
                    && let Some(range) =
                        find_word_in_line(directive_line, &source_account, start_line)
                {
                    references.push(EditorReference {
                        range,
                        kind: ReferenceKind::Account,
                        is_definition: false,
                        context: Some("pad source".to_string()),
                    });
                }
            }
            Directive::Note(note) => {
                let note_account = note.account.to_string();
                if note_account == account
                    && let Some(range) =
                        find_word_in_line(directive_line, &note_account, start_line)
                {
                    references.push(EditorReference {
                        range,
                        kind: ReferenceKind::Account,
                        is_definition: false,
                        context: Some("note".to_string()),
                    });
                }
            }
            Directive::Document(doc) => {
                let doc_account = doc.account.to_string();
                if doc_account == account
                    && let Some(range) = find_word_in_line(directive_line, &doc_account, start_line)
                {
                    references.push(EditorReference {
                        range,
                        kind: ReferenceKind::Account,
                        is_definition: false,
                        context: Some("document".to_string()),
                    });
                }
            }
            Directive::Transaction(txn) => {
                // Check postings - they're on subsequent lines
                for (i, posting) in txn.postings.iter().enumerate() {
                    let posting_account = posting.account.to_string();
                    if posting_account == account {
                        let posting_line = start_line + 1 + i as u32;
                        if let Some(line_text) = source.lines().nth(posting_line as usize)
                            && let Some(range) =
                                find_word_in_line(line_text, &posting_account, posting_line)
                        {
                            references.push(EditorReference {
                                range,
                                kind: ReferenceKind::Account,
                                is_definition: false,
                                context: Some("posting".to_string()),
                            });
                        }
                    }
                }
            }
            _ => {}
        }
    }

    EditorReferencesResult {
        symbol: account.to_string(),
        kind: ReferenceKind::Account,
        references,
    }
}

/// Find all references to a currency.
fn find_currency_references(
    currency: &str,
    source: &str,
    parse_result: &ParseResult,
    line_index: &LineIndex,
) -> EditorReferencesResult {
    let mut references = Vec::new();

    for spanned_directive in &parse_result.directives {
        let (start_line, _) = line_index.offset_to_position(spanned_directive.span.start);
        let directive_line = get_line(source, start_line as usize);

        match &spanned_directive.value {
            Directive::Commodity(comm) => {
                if comm.currency.as_ref() == currency
                    && let Some(range) = find_word_in_line(directive_line, currency, start_line)
                {
                    references.push(EditorReference {
                        range,
                        kind: ReferenceKind::Currency,
                        is_definition: true,
                        context: Some("commodity".to_string()),
                    });
                }
            }
            Directive::Open(open) => {
                for curr in &open.currencies {
                    if curr.as_ref() == currency
                        && let Some(range) = find_word_in_line(directive_line, currency, start_line)
                    {
                        references.push(EditorReference {
                            range,
                            kind: ReferenceKind::Currency,
                            is_definition: false,
                            context: Some("open".to_string()),
                        });
                    }
                }
            }
            Directive::Balance(bal) => {
                if bal.amount.currency.as_ref() == currency
                    && let Some(range) = find_word_in_line(directive_line, currency, start_line)
                {
                    references.push(EditorReference {
                        range,
                        kind: ReferenceKind::Currency,
                        is_definition: false,
                        context: Some("balance".to_string()),
                    });
                }
            }
            Directive::Price(price) => {
                if price.currency.as_ref() == currency
                    && let Some(range) = find_word_in_line(directive_line, currency, start_line)
                {
                    references.push(EditorReference {
                        range,
                        kind: ReferenceKind::Currency,
                        is_definition: false,
                        context: Some("price".to_string()),
                    });
                }
                if price.amount.currency.as_ref() == currency {
                    // Find second occurrence
                    if let Some(range) =
                        find_nth_word_in_line(directive_line, currency, start_line, 1)
                    {
                        references.push(EditorReference {
                            range,
                            kind: ReferenceKind::Currency,
                            is_definition: false,
                            context: Some("price amount".to_string()),
                        });
                    }
                }
            }
            Directive::Transaction(txn) => {
                for (i, posting) in txn.postings.iter().enumerate() {
                    if let Some(ref units) = posting.units
                        && let Some(curr) = units.currency()
                        && curr == currency
                    {
                        let posting_line = start_line + 1 + i as u32;
                        if let Some(line_text) = source.lines().nth(posting_line as usize)
                            && let Some(range) =
                                find_word_in_line(line_text, currency, posting_line)
                        {
                            references.push(EditorReference {
                                range,
                                kind: ReferenceKind::Currency,
                                is_definition: false,
                                context: Some("posting".to_string()),
                            });
                        }
                    }
                }
            }
            _ => {}
        }
    }

    EditorReferencesResult {
        symbol: currency.to_string(),
        kind: ReferenceKind::Currency,
        references,
    }
}

/// Find all references to a payee.
fn find_payee_references(
    payee: &str,
    source: &str,
    parse_result: &ParseResult,
    line_index: &LineIndex,
) -> EditorReferencesResult {
    let mut references = Vec::new();

    for spanned_directive in &parse_result.directives {
        if let Directive::Transaction(txn) = &spanned_directive.value
            && let Some(ref txn_payee) = txn.payee
            && txn_payee == payee
        {
            let (start_line, _) = line_index.offset_to_position(spanned_directive.span.start);
            let line_text = get_line(source, start_line as usize);

            // Find the quoted payee in the line
            let range =
                if let Some(range) = find_quoted_string_in_line(line_text, payee, start_line) {
                    range
                } else {
                    // Fallback: use line start to payee length
                    EditorRange {
                        start_line,
                        start_character: 0,
                        end_line: start_line,
                        end_character: payee.len() as u32,
                    }
                };

            references.push(EditorReference {
                range,
                kind: ReferenceKind::Payee,
                is_definition: references.is_empty(), // First occurrence is "definition"
                context: Some("transaction".to_string()),
            });
        }
    }

    EditorReferencesResult {
        symbol: payee.to_string(),
        kind: ReferenceKind::Payee,
        references,
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use rustledger_parser::parse;

    #[test]
    fn test_get_references_account() {
        let source = r#"2024-01-01 open Assets:Bank USD
2024-01-15 balance Assets:Bank 100.00 USD
2024-01-20 * "Transfer"
  Assets:Bank  50.00 USD
  Income:Salary
"#;
        let result = parse(source);
        let cache = EditorCache::new(source, &result);

        let refs = get_references_cached(source, 0, 20, &result, &cache);
        assert!(refs.is_some());

        let refs = refs.unwrap();
        assert_eq!(refs.symbol, "Assets:Bank");
        assert_eq!(refs.kind, ReferenceKind::Account);
        assert!(refs.references.len() >= 3); // open, balance, posting
    }

    #[test]
    fn test_get_references_currency() {
        let source = r"2024-01-01 commodity USD
2024-01-01 open Assets:Bank USD
2024-01-15 balance Assets:Bank 100.00 USD
";
        let result = parse(source);
        let cache = EditorCache::new(source, &result);

        let refs = get_references_cached(source, 0, 21, &result, &cache);
        assert!(refs.is_some());

        let refs = refs.unwrap();
        assert_eq!(refs.symbol, "USD");
        assert_eq!(refs.kind, ReferenceKind::Currency);
        assert!(refs.references.len() >= 3); // commodity, open, balance
    }
}
