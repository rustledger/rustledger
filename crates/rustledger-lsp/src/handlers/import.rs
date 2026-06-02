//! Import review integration for the LSP.
//!
//! Scans transactions for `import-*` metadata (produced by the enriched
//! import pipeline) and provides:
//!
//! - **Diagnostics**: hints/warnings for imported transactions based on confidence
//! - **Code actions**: accept categorization, change account, batch accept
//! - **Code lens**: summary counts of imported/pending/duplicate transactions

use lsp_types::{
    CodeAction, CodeActionKind, CodeLens, Command, Diagnostic, DiagnosticSeverity, Position, Range,
};
use rustledger_core::{Directive, MetaValue};
use rustledger_parser::Spanned;

use super::utils::{LineIndex, PositionEncoding, ranges_overlap};

/// Convert a byte offset to an LSP Position using a LineIndex.
fn to_position(line_index: &LineIndex, offset: usize) -> Position {
    let (line, col) = line_index.offset_to_position(offset);
    Position {
        line,
        character: col,
    }
}

/// Metadata key for import confidence (set by enriched import pipeline).
const META_CONFIDENCE: &str = "import-confidence";
/// Metadata key for import method (rule, merchant-dict, ml, llm, default).
const META_METHOD: &str = "import-method";

/// Generate diagnostics for imported transactions based on their confidence.
///
/// - confidence > 0.9 → Hint ("Imported via rule: Expenses:Groceries")
/// - confidence 0.5–0.9 → Information ("Review: Expenses:Dining (72%)")
/// - confidence < 0.5 → Warning ("Low confidence: Expenses:Unknown")
pub fn import_diagnostics(
    directives: &[Spanned<Directive>],
    source: &str,
    encoding: PositionEncoding,
) -> Vec<Diagnostic> {
    let line_index = LineIndex::new(source, encoding);
    let mut diagnostics = Vec::new();

    for spanned in directives {
        let Directive::Transaction(txn) = &spanned.value else {
            continue;
        };

        let Some(confidence) = txn.meta.get(META_CONFIDENCE).and_then(meta_to_f64) else {
            continue;
        };

        let method = txn
            .meta
            .get(META_METHOD)
            .and_then(meta_to_str)
            .unwrap_or("unknown");

        // Find the contra-account (the categorized posting, not the bank account)
        let contra_account = txn
            .postings
            .get(1)
            .map(|p| p.account.as_str())
            .unwrap_or("unknown");

        let start = to_position(&line_index, spanned.span.start);
        let end = to_position(&line_index, spanned.span.end.min(source.len()));
        let range = Range { start, end };

        let (severity, message) = if confidence > 0.9 {
            (
                DiagnosticSeverity::HINT,
                format!("Imported ({method}): {contra_account}"),
            )
        } else if confidence >= 0.5 {
            (
                DiagnosticSeverity::INFORMATION,
                format!(
                    "Review ({method}, {:.0}%): {contra_account}",
                    confidence * 100.0
                ),
            )
        } else {
            (
                DiagnosticSeverity::WARNING,
                format!(
                    "Low confidence ({:.0}%): {contra_account} — consider recategorizing",
                    confidence * 100.0
                ),
            )
        };

        diagnostics.push(Diagnostic {
            range,
            severity: Some(severity),
            source: Some("rustledger-import".to_string()),
            message,
            ..Default::default()
        });
    }

    diagnostics
}

/// Generate code actions for imported transactions in the given range.
///
/// Offers:
/// - "Accept categorization" for individual transactions
/// - "Accept all high-confidence imports" for batch operations
pub fn import_code_actions(
    directives: &[Spanned<Directive>],
    source: &str,
    range: Range,
    encoding: PositionEncoding,
) -> Vec<CodeAction> {
    let line_index = LineIndex::new(source, encoding);
    let mut actions = Vec::new();
    let mut high_confidence_count = 0;

    for spanned in directives {
        let Directive::Transaction(txn) = &spanned.value else {
            continue;
        };

        let Some(confidence) = txn.meta.get(META_CONFIDENCE).and_then(meta_to_f64) else {
            continue;
        };

        if confidence > 0.9 {
            high_confidence_count += 1;
        }

        let start = to_position(&line_index, spanned.span.start);
        let end = to_position(&line_index, spanned.span.end.min(source.len()));
        let txn_range = Range { start, end };

        // Only offer actions for transactions that overlap the selection
        if !ranges_overlap(range, txn_range) {
            continue;
        }

        let contra_account = txn
            .postings
            .get(1)
            .map(|p| p.account.to_string())
            .unwrap_or_default();

        actions.push(CodeAction {
            title: format!("Accept import: {contra_account}"),
            kind: Some(CodeActionKind::QUICKFIX),
            command: Some(Command {
                title: "Accept import".to_string(),
                command: "rledger.importAccept".to_string(),
                arguments: Some(vec![serde_json::json!({
                    "line": start.line,
                })]),
            }),
            ..Default::default()
        });
    }

    // Batch accept action
    if high_confidence_count > 1 {
        actions.push(CodeAction {
            title: format!("Accept all {high_confidence_count} high-confidence imports"),
            kind: Some(CodeActionKind::QUICKFIX),
            command: Some(Command {
                title: "Accept all high-confidence".to_string(),
                command: "rledger.importAcceptAll".to_string(),
                arguments: None,
            }),
            ..Default::default()
        });
    }

    actions
}

/// Generate code lens for import summary.
///
/// Shows a summary line above the first imported transaction:
/// "N imported | M need review | K duplicates"
pub fn import_code_lens(
    directives: &[Spanned<Directive>],
    source: &str,
    encoding: PositionEncoding,
) -> Vec<CodeLens> {
    let line_index = LineIndex::new(source, encoding);
    let mut total = 0u32;
    let mut needs_review = 0u32;
    let mut first_import_line: Option<Position> = None;

    for spanned in directives {
        let Directive::Transaction(txn) = &spanned.value else {
            continue;
        };

        let Some(confidence) = txn.meta.get(META_CONFIDENCE).and_then(meta_to_f64) else {
            continue;
        };

        total += 1;
        if confidence < 0.9 {
            needs_review += 1;
        }

        if first_import_line.is_none() {
            first_import_line = Some(to_position(&line_index, spanned.span.start));
        }
    }

    if total == 0 {
        return vec![];
    }

    let Some(pos) = first_import_line else {
        return vec![];
    };

    let title = if needs_review > 0 {
        format!("{total} imported | {needs_review} need review")
    } else {
        format!("{total} imported | all accepted")
    };

    vec![CodeLens {
        range: Range {
            start: Position {
                line: pos.line,
                character: 0,
            },
            end: Position {
                line: pos.line,
                character: 0,
            },
        },
        command: Some(Command {
            title,
            command: "rustledger.importSummary".to_string(),
            arguments: None,
        }),
        data: None,
    }]
}

/// Extract f64 from MetaValue.
fn meta_to_f64(v: &MetaValue) -> Option<f64> {
    match v {
        MetaValue::Number(d) => {
            use rust_decimal::prelude::ToPrimitive;
            d.to_f64()
        }
        _ => None,
    }
}

/// Extract &str from MetaValue.
fn meta_to_str(v: &MetaValue) -> Option<&str> {
    match v {
        MetaValue::String(s) => Some(s.as_str()),
        _ => None,
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use rust_decimal::Decimal;
    use rustledger_core::{Metadata, Posting, Transaction, naive_date};
    use rustledger_parser::Span;
    use std::str::FromStr;

    fn make_imported_txn(confidence: f64, method: &str, account: &str) -> Spanned<Directive> {
        let date = naive_date(2024, 1, 15).unwrap();
        let mut meta = Metadata::default();
        meta.insert(
            META_CONFIDENCE.to_string(),
            MetaValue::Number(Decimal::from_str(&confidence.to_string()).unwrap()),
        );
        meta.insert(
            META_METHOD.to_string(),
            MetaValue::String(method.to_string()),
        );

        let txn = Transaction {
            date,
            flag: '*',
            payee: None,
            narration: "Test".into(),
            tags: vec![],
            links: vec![],
            meta,
            postings: vec![
                rustledger_core::Spanned::synthesized(Posting::new(
                    "Assets:Bank",
                    rustledger_core::Amount::new(Decimal::from_str("-50").unwrap(), "USD"),
                )),
                rustledger_core::Spanned::synthesized(Posting::new(
                    account,
                    rustledger_core::Amount::new(Decimal::from_str("50").unwrap(), "USD"),
                )),
            ],
            trailing_comments: vec![],
        };

        Spanned {
            value: Directive::Transaction(txn),
            span: Span { start: 0, end: 100 },
            file_id: 0,
        }
    }

    fn make_source() -> String {
        // Source text long enough for the spans
        " ".repeat(200)
    }

    #[test]
    fn diagnostics_high_confidence_is_hint() {
        let source = make_source();
        let directives = vec![make_imported_txn(0.95, "rule", "Expenses:Groceries")];
        let diags = import_diagnostics(&directives, &source, PositionEncoding::Utf16);
        assert_eq!(diags.len(), 1);
        assert_eq!(diags[0].severity, Some(DiagnosticSeverity::HINT));
        assert!(diags[0].message.contains("Expenses:Groceries"));
    }

    #[test]
    fn diagnostics_medium_confidence_is_info() {
        let source = make_source();
        let directives = vec![make_imported_txn(0.72, "ml", "Expenses:Dining")];
        let diags = import_diagnostics(&directives, &source, PositionEncoding::Utf16);
        assert_eq!(diags.len(), 1);
        assert_eq!(diags[0].severity, Some(DiagnosticSeverity::INFORMATION));
        assert!(diags[0].message.contains("72%"));
    }

    #[test]
    fn diagnostics_low_confidence_is_warning() {
        let source = make_source();
        let directives = vec![make_imported_txn(0.3, "default", "Expenses:Unknown")];
        let diags = import_diagnostics(&directives, &source, PositionEncoding::Utf16);
        assert_eq!(diags.len(), 1);
        assert_eq!(diags[0].severity, Some(DiagnosticSeverity::WARNING));
        assert!(diags[0].message.contains("recategorizing"));
    }

    #[test]
    fn diagnostics_skips_non_imported() {
        let source = make_source();
        let date = naive_date(2024, 1, 15).unwrap();
        let txn = Transaction::new(date, "Not imported");
        let directives = vec![Spanned {
            value: Directive::Transaction(txn),
            span: Span { start: 0, end: 50 },
            file_id: 0,
        }];
        let diags = import_diagnostics(&directives, &source, PositionEncoding::Utf16);
        assert!(diags.is_empty());
    }

    #[test]
    fn code_lens_shows_summary() {
        let source = make_source();
        let directives = vec![
            make_imported_txn(0.95, "rule", "Expenses:Groceries"),
            make_imported_txn(0.6, "ml", "Expenses:Dining"),
            make_imported_txn(0.3, "default", "Expenses:Unknown"),
        ];
        let lenses = import_code_lens(&directives, &source, PositionEncoding::Utf16);
        assert_eq!(lenses.len(), 1);
        let title = &lenses[0].command.as_ref().unwrap().title;
        assert!(title.contains("3 imported"));
        assert!(title.contains("2 need review"));
    }

    #[test]
    fn code_lens_all_accepted() {
        let source = make_source();
        let directives = vec![
            make_imported_txn(0.95, "rule", "Expenses:Groceries"),
            make_imported_txn(0.99, "rule", "Expenses:Dining"),
        ];
        let lenses = import_code_lens(&directives, &source, PositionEncoding::Utf16);
        assert_eq!(lenses.len(), 1);
        let title = &lenses[0].command.as_ref().unwrap().title;
        assert!(title.contains("all accepted"));
    }

    #[test]
    fn code_lens_empty_for_no_imports() {
        let source = make_source();
        let directives = vec![];
        let lenses = import_code_lens(&directives, &source, PositionEncoding::Utf16);
        assert!(lenses.is_empty());
    }

    // ===== Code action tests =====

    fn make_imported_txn_at(
        confidence: f64,
        method: &str,
        account: &str,
        start: usize,
        end: usize,
    ) -> Spanned<Directive> {
        let date = naive_date(2024, 1, 15).unwrap();
        let mut meta = Metadata::default();
        meta.insert(
            META_CONFIDENCE.to_string(),
            MetaValue::Number(Decimal::from_str(&confidence.to_string()).unwrap()),
        );
        meta.insert(
            META_METHOD.to_string(),
            MetaValue::String(method.to_string()),
        );

        let txn = Transaction {
            date,
            flag: '*',
            payee: None,
            narration: "Test".into(),
            tags: vec![],
            links: vec![],
            meta,
            postings: vec![
                rustledger_core::Spanned::synthesized(Posting::new(
                    "Assets:Bank",
                    rustledger_core::Amount::new(Decimal::from_str("-50").unwrap(), "USD"),
                )),
                rustledger_core::Spanned::synthesized(Posting::new(
                    account,
                    rustledger_core::Amount::new(Decimal::from_str("50").unwrap(), "USD"),
                )),
            ],
            trailing_comments: vec![],
        };

        Spanned {
            value: Directive::Transaction(txn),
            span: Span { start, end },
            file_id: 0,
        }
    }

    #[test]
    fn code_actions_appear_for_txns_in_range() {
        // Source: 400 chars, two txns at different positions
        let source = " ".repeat(400);
        let directives = vec![
            make_imported_txn_at(0.95, "rule", "Expenses:Groceries", 0, 100),
            make_imported_txn_at(0.6, "ml", "Expenses:Dining", 200, 300),
        ];

        // Request actions covering only the first transaction
        let range = Range {
            start: Position {
                line: 0,
                character: 0,
            },
            end: Position {
                line: 0,
                character: 50,
            },
        };
        let actions = import_code_actions(&directives, &source, range, PositionEncoding::Utf16);

        // Should have action for first txn + batch action (2 high-confidence)
        let accept_actions: Vec<_> = actions
            .iter()
            .filter(|a| a.title.starts_with("Accept import:"))
            .collect();
        assert_eq!(accept_actions.len(), 1);
        assert!(accept_actions[0].title.contains("Expenses:Groceries"));
    }

    #[test]
    fn code_actions_not_outside_range() {
        let source = " ".repeat(400);
        let directives = vec![make_imported_txn_at(
            0.95,
            "rule",
            "Expenses:Groceries",
            200,
            300,
        )];

        // Request actions for range 0..50 which does NOT overlap the txn at 200..300
        // Line index: since source is all spaces on line 0, byte 200 is still line 0, char 200
        // So we need a range that ends before char 200
        let range = Range {
            start: Position {
                line: 0,
                character: 0,
            },
            end: Position {
                line: 0,
                character: 50,
            },
        };
        let actions = import_code_actions(&directives, &source, range, PositionEncoding::Utf16);

        // No accept actions for individual txns (only batch if applicable)
        let accept_actions: Vec<_> = actions
            .iter()
            .filter(|a| a.title.starts_with("Accept import:"))
            .collect();
        assert!(accept_actions.is_empty());
    }

    #[test]
    fn code_actions_batch_accept_count() {
        let source = " ".repeat(600);
        let directives = vec![
            make_imported_txn_at(0.95, "rule", "Expenses:Groceries", 0, 100),
            make_imported_txn_at(0.99, "rule", "Expenses:Dining", 100, 200),
            make_imported_txn_at(0.3, "default", "Expenses:Unknown", 200, 300),
        ];

        // Request actions covering all transactions
        let range = Range {
            start: Position {
                line: 0,
                character: 0,
            },
            end: Position {
                line: 0,
                character: 599,
            },
        };
        let actions = import_code_actions(&directives, &source, range, PositionEncoding::Utf16);

        // Should have batch accept with count = 2 (only the two > 0.9)
        let batch_action = actions
            .iter()
            .find(|a| a.title.contains("Accept all"))
            .expect("batch action should exist");
        assert!(batch_action.title.contains("2"));
    }

    #[test]
    fn code_actions_no_batch_when_single_high_confidence() {
        let source = " ".repeat(400);
        let directives = vec![
            make_imported_txn_at(0.95, "rule", "Expenses:Groceries", 0, 100),
            make_imported_txn_at(0.3, "default", "Expenses:Unknown", 100, 200),
        ];

        let range = Range {
            start: Position {
                line: 0,
                character: 0,
            },
            end: Position {
                line: 0,
                character: 399,
            },
        };
        let actions = import_code_actions(&directives, &source, range, PositionEncoding::Utf16);

        // Only 1 high confidence → no batch action
        let batch_actions: Vec<_> = actions
            .iter()
            .filter(|a| a.title.contains("Accept all"))
            .collect();
        assert!(batch_actions.is_empty());
    }

    #[test]
    fn ranges_overlap_basic() {
        let a = Range {
            start: Position {
                line: 0,
                character: 0,
            },
            end: Position {
                line: 0,
                character: 10,
            },
        };
        let b = Range {
            start: Position {
                line: 0,
                character: 5,
            },
            end: Position {
                line: 0,
                character: 15,
            },
        };
        assert!(ranges_overlap(a, b));
    }

    #[test]
    fn ranges_no_overlap() {
        let a = Range {
            start: Position {
                line: 0,
                character: 0,
            },
            end: Position {
                line: 0,
                character: 5,
            },
        };
        let b = Range {
            start: Position {
                line: 0,
                character: 10,
            },
            end: Position {
                line: 0,
                character: 15,
            },
        };
        assert!(!ranges_overlap(a, b));
    }

    /// LSP half-open `Range.end` semantics: adjacent ranges where
    /// `a.end == b.start` are NOT overlapping. Pre-round-17 the import
    /// module had a private `ranges_overlap` with strict `<` semantics
    /// that returned `true` for this boundary case; the round-17
    /// canonicalization hoisted the helper to `utils::ranges_overlap`
    /// with the spec-correct `<=` semantics. This test pins the new
    /// behavior so a future revert (or accidental re-introduction of
    /// the old `<` predicate) is caught.
    #[test]
    fn ranges_adjacent_are_not_overlapping() {
        let a = Range {
            start: Position::new(0, 0),
            end: Position::new(0, 10),
        };
        let b = Range {
            start: Position::new(0, 10),
            end: Position::new(0, 20),
        };
        assert!(
            !ranges_overlap(a, b),
            "adjacent ranges (a.end == b.start) must not overlap under LSP half-open semantics"
        );
        assert!(
            !ranges_overlap(b, a),
            "adjacency is symmetric — swapping the args must not flip the result"
        );

        // Cross-line adjacency: a ends on line 1 col 0 (= start of
        // line 1), b starts at line 1 col 0. Same not-overlapping.
        let a = Range {
            start: Position::new(0, 0),
            end: Position::new(1, 0),
        };
        let b = Range {
            start: Position::new(1, 0),
            end: Position::new(2, 0),
        };
        assert!(!ranges_overlap(a, b));
    }

    #[test]
    fn diagnostics_source_is_set() {
        let source = make_source();
        let directives = vec![make_imported_txn(0.95, "rule", "Expenses:Groceries")];
        let diags = import_diagnostics(&directives, &source, PositionEncoding::Utf16);
        assert_eq!(diags[0].source.as_deref(), Some("rustledger-import"));
    }
}
