//! Find references support for the editor.

use rustledger_core::Directive;
use rustledger_parser::ParseResult;

use crate::types::{EditorRange, EditorReference, EditorReferencesResult, ReferenceKind};

use super::helpers::{
    find_quoted_string_in_line, find_word_in_line, get_line, get_symbol_at_position,
    is_currency_like,
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
    let word = get_symbol_at_position(source, line, character, parse_result)?;

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
///
/// Walks the parser's `currency_occurrences` (every currency token, with its
/// exact span), as the LSP does. A text search for the name in each
/// directive's line used to land on the wrong token: for a one-letter
/// currency `B` on `open Assets:X BRK.B,B` it found the `B` inside `BRK.B`,
/// because `.` ends a word. The token index also leaves out one-letter flags
/// (`T` in `2024-01-16 T "x"`), which are not currencies, and reaches cost,
/// price-annotation and metadata currencies, which the text search skipped.
fn find_currency_references(
    currency: &str,
    parse_result: &ParseResult,
    line_index: &LineIndex,
) -> EditorReferencesResult {
    let mut references = Vec::new();
    let directives = &parse_result.directives;
    let occurrences = &parse_result.currency_occurrences;

    for occurrence in occurrences.iter().filter(|o| o.value == currency) {
        // The directive holding the token: directives are in source order,
        // so the last one starting at or before the token is the candidate.
        let holder = directives
            .partition_point(|d| d.span.start <= occurrence.span.start)
            .checked_sub(1)
            .map(|i| &directives[i])
            .filter(|d| occurrence.span.end <= d.span.end);
        // Whether the token is the first currency token of its directive:
        // the declared currency of a `commodity`, the priced one of a `price`.
        // Occurrences are in source order, so the first one at or after the
        // directive's start is found by binary search; only those two kinds
        // ask, so the walk stays O(n log n) (a linear scan per match made it
        // quadratic).
        let first_in_holder = |d: &rustledger_parser::Spanned<Directive>| {
            let i = occurrences.partition_point(|o| o.span.start < d.span.start);
            occurrences
                .get(i)
                .is_some_and(|o| o.span == occurrence.span)
        };
        // A token's context is its directive's kind. That includes currency
        // values in a directive's metadata: a currency in a `commodity`'s
        // metadata gets "commodity" (not a definition, since it is not the
        // first token), and one in a `price`'s metadata gets "price amount".
        let (is_definition, context) = match holder.map(|d| (d, &d.value)) {
            Some((d, Directive::Commodity(_))) => (first_in_holder(d), Some("commodity")),
            Some((d, Directive::Price(_))) if first_in_holder(d) => (false, Some("price")),
            Some((_, Directive::Price(_))) => (false, Some("price amount")),
            Some((_, Directive::Open(_))) => (false, Some("open")),
            Some((_, Directive::Balance(_))) => (false, Some("balance")),
            Some((_, Directive::Transaction(_))) => (false, Some("posting")),
            _ => (false, None),
        };
        let (start_line, start_character) = line_index.offset_to_position(occurrence.span.start);
        let (end_line, end_character) = line_index.offset_to_position(occurrence.span.end);
        references.push(EditorReference {
            range: EditorRange {
                start_line,
                start_character,
                end_line,
                end_character,
            },
            kind: ReferenceKind::Currency,
            is_definition,
            context: context.map(str::to_string),
        });
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

    /// References on a one-letter currency land on its own tokens: not on
    /// the `B` inside `BRK.B`, and not on a `T` flag (#2807 review).
    #[test]
    fn test_get_references_one_letter_currency_tokens() {
        let source = "2024-01-01 commodity B\n\
                      2024-01-01 open Assets:X BRK.B,B\n\
                      2024-01-01 commodity T\n\
                      2024-01-16 T \"Transfer\"\n  \
                      Assets:X  1 T\n  \
                      Assets:Y\n";
        let result = parse(source);
        let cache = EditorCache::new(source, &result);
        let ranges = |line, character| {
            get_references_cached(source, line, character, &result, &cache).map(|refs| {
                refs.references
                    .iter()
                    .map(|r| {
                        (
                            r.range.start_line,
                            r.range.start_character,
                            r.range.end_character,
                            r.is_definition,
                            r.context.clone(),
                        )
                    })
                    .collect::<Vec<_>>()
            })
        };
        let ctx = |s: &str| Some(s.to_string());
        assert_eq!(
            ranges(0, 21),
            Some(vec![
                (0, 21, 22, true, ctx("commodity")),
                (1, 31, 32, false, ctx("open")),
            ])
        );
        assert_eq!(
            ranges(2, 21),
            Some(vec![
                (2, 21, 22, true, ctx("commodity")),
                (4, 14, 15, false, ctx("posting")),
            ])
        );
        assert_eq!(ranges(3, 11), None, "the T flag is no symbol");
    }

    /// Cost and price currencies are references too, and a `price`
    /// directive's two currencies get their own contexts.
    #[test]
    fn test_get_references_currency_cost_and_price() {
        let source = "2024-01-01 price HOOL 10 USD\n\
                      2024-01-02 * \"Buy\"\n  \
                      Assets:X  1 HOOL {10 USD} @ 10 USD\n  \
                      Assets:Y\n";
        let result = parse(source);
        let cache = EditorCache::new(source, &result);
        let refs = get_references_cached(source, 0, 25, &result, &cache).expect("references");
        let summary: Vec<_> = refs
            .references
            .iter()
            .map(|r| {
                (
                    r.range.start_line,
                    r.range.start_character,
                    r.context.clone(),
                )
            })
            .collect();
        assert_eq!(
            summary,
            vec![
                (0, 25, Some("price amount".to_string())),
                (2, 23, Some("posting".to_string())),
                (2, 33, Some("posting".to_string())),
            ]
        );
    }

    /// The currency walk is not quadratic in the number of matches: each
    /// match resolves its directive and its "first token" by binary search.
    /// This ledger has 60k matches across `commodity`, `price` and `open`
    /// directives, which all paid the old per-match linear scan. In a debug
    /// test build the walk takes about 90 ms; with the old scan put back it
    /// took about 13 s and tripped the bound. The bound is loose on purpose so
    /// a slow machine does not trip it.
    #[test]
    fn test_get_references_currency_is_not_quadratic() {
        use std::fmt::Write as _;
        const N: usize = 20_000;
        let mut source = String::from("2024-01-01 commodity USD\n");
        for i in 0..N {
            writeln!(source, "2024-01-01 open Assets:A{i} USD").unwrap();
            writeln!(source, "2024-01-02 price USD 1 EUR").unwrap();
            writeln!(source, "2024-01-03 commodity C{i}\n  quote: USD").unwrap();
        }
        let result = parse(&source);
        assert!(result.errors.is_empty(), "{:?}", result.errors.first());
        let cache = EditorCache::new(&source, &result);
        let started = std::time::Instant::now();
        let refs = get_references_cached(&source, 0, 21, &result, &cache).expect("references");
        let elapsed = started.elapsed();
        assert_eq!(refs.references.len(), 1 + 3 * N);
        assert!(refs.references[0].is_definition);
        assert_eq!(refs.references[2].context.as_deref(), Some("price"));
        assert_eq!(refs.references[3].context.as_deref(), Some("commodity"));
        assert!(!refs.references[3].is_definition, "a metadata currency");
        assert!(
            elapsed < std::time::Duration::from_secs(5),
            "currency references took {elapsed:?} for {} matches",
            refs.references.len()
        );
    }
}
