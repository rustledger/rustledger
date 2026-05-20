//! Inlay hints handler for inline annotations.
//!
//! Provides inlay hints for:
//! - Inferred amounts on postings without explicit amounts
//! - Running balances (future enhancement)
//!
//! Supports resolve for lazy-loading rich tooltips with account details.

use lsp_types::{InlayHint, InlayHintKind, InlayHintLabel, InlayHintParams, Position};
use rustledger_booking::interpolate;
use rustledger_core::{Decimal, Directive, IncompleteAmount, SYNTHESIZED_FILE_ID};
use rustledger_parser::ParseResult;
use std::collections::HashMap;

use super::utils::LineIndex;

/// Handle an inlay hints request.
pub fn handle_inlay_hints(
    params: &InlayHintParams,
    source: &str,
    parse_result: &ParseResult,
) -> Option<Vec<InlayHint>> {
    let range = params.range;
    let uri = params.text_document.uri.as_str();
    let mut hints = Vec::new();
    let lines: Vec<&str> = source.lines().collect();
    // Build the line index once: O(n) up front, O(log lines) per
    // offset lookup. Without it the per-directive + per-posting
    // lookups below scale quadratically with file size.
    let line_index = LineIndex::new(source);

    for spanned in &parse_result.directives {
        let Directive::Transaction(txn) = &spanned.value else {
            continue;
        };
        let (start_line, _) = line_index.offset_to_position(spanned.span.start);
        if start_line > range.end.line {
            continue;
        }

        // Fast path: a transaction with no fully-missing postings
        // has no inferred-amount hint to emit, and there's no point
        // running the interpolator (which clones the transaction
        // internally). The common case is fully-explicit
        // transactions, so this gate is a meaningful win on large
        // files where inlay hints are recomputed on every keystroke.
        //
        // We gate on `units.is_none()` rather than "any non-Complete"
        // because the inlay-hint UX only renders for fully-missing
        // postings — see the filter further down.
        if !txn.postings.iter().any(|p| p.units.is_none()) {
            continue;
        }

        // Delegate inference to the canonical booking interpolator.
        // The previous bespoke implementation (`calculate_inferred_amount`)
        // only handled the simplest case (exactly one missing posting,
        // exactly one currency) — multi-currency transactions and
        // postings with cost specs silently emitted zero hints.
        //
        // `InterpolationError` (e.g. MultipleMissing, unbalanced) is
        // silently dropped: no hints for an under-specified
        // transaction is the right outcome.
        let Ok(filled) = interpolate(txn) else {
            continue;
        };

        // Walk SOURCE postings (not `filled.filled_indices`) and
        // locate each fill by matching span. Three properties fall
        // out of this design:
        //
        // 1. **Source-order, deterministic output.** The
        //    interpolator's `filled_indices` is built from
        //    HashMap-driven iteration whose order is unspecified;
        //    walking source postings gives a stable order the
        //    client can rely on.
        //
        // 2. **Naturally restricts to fully-missing postings.**
        //    `NumberOnly`/`CurrencyOnly` source postings already
        //    display one half on screen, so appending the other
        //    half at line-end would visually duplicate the typed
        //    text (`Assets:Cash USD  -50.00 USD`) or wrongly order
        //    number-then-currency. The bespoke pre-refactor
        //    implementation only emitted hints for fully-missing
        //    postings, and we deliberately preserve that UX.
        //
        // 3. **Sidesteps prune-shift bugs.** Interpolate's prune
        //    step removes zero-amount fills from
        //    `result.postings`, which shifts subsequent fills'
        //    positions; `filled_indices` is then result-relative,
        //    not source-relative. Matching by span — preserved
        //    across `interpolate`'s clone — sidesteps that issue
        //    entirely. (In current code paths the zero-fill case is
        //    structurally unreachable, but the design is robust to
        //    future changes.)
        for source_posting in &txn.postings {
            if source_posting.units.is_some() {
                continue;
            }
            if source_posting.file_id == SYNTHESIZED_FILE_ID {
                continue;
            }

            let (posting_line, _) = line_index.offset_to_position(source_posting.span.start);
            if posting_line < range.start.line || posting_line > range.end.line {
                continue;
            }

            // Match the filled version of this source posting by
            // span. `interpolate` clones source postings and
            // preserves their spans, so byte-offset equality
            // identifies the same posting reliably. If no match —
            // the slot filled to zero and got pruned — emit no
            // hint.
            let Some(filled_posting) = filled
                .transaction
                .postings
                .iter()
                .find(|p| p.span.start == source_posting.span.start)
            else {
                continue;
            };

            let Some(IncompleteAmount::Complete(amount)) = &filled_posting.units else {
                debug_assert!(
                    false,
                    "interpolate: fully-missing source posting did not fill to Complete: {:?}",
                    filled_posting.units
                );
                continue;
            };

            let Some(line) = lines.get(posting_line as usize) else {
                continue;
            };

            // Position hint at the end of the account name
            let trimmed = line.trim();
            let indent = line.len() - line.trim_start().len();
            let end_col = indent + trimmed.len();

            // Store data for resolve - include account for rich tooltip
            let data = serde_json::json!({
                "uri": uri,
                "kind": "inferred_amount",
                "account": source_posting.account.to_string(),
                "amount": amount.number.to_string(),
                "currency": amount.currency.to_string(),
            });

            hints.push(InlayHint {
                position: Position::new(posting_line, end_col as u32),
                label: InlayHintLabel::String(format!("  {} {}", amount.number, amount.currency)),
                kind: Some(InlayHintKind::TYPE),
                text_edits: None,
                tooltip: None, // Resolved lazily
                padding_left: Some(true),
                padding_right: None,
                data: Some(data),
            });
        }
    }

    if hints.is_empty() { None } else { Some(hints) }
}

/// Handle an inlay hint resolve request.
/// Adds rich tooltip with account balance information.
pub fn handle_inlay_hint_resolve(hint: InlayHint, parse_result: &ParseResult) -> InlayHint {
    let mut resolved = hint.clone();

    // Check if we have data to resolve
    if let Some(data) = &hint.data
        && let Some(kind) = data.get("kind").and_then(|v| v.as_str())
        && kind == "inferred_amount"
    {
        let account = data.get("account").and_then(|v| v.as_str()).unwrap_or("");
        let amount = data.get("amount").and_then(|v| v.as_str()).unwrap_or("");
        let currency = data.get("currency").and_then(|v| v.as_str()).unwrap_or("");

        // Build rich tooltip with account information
        let tooltip = build_account_tooltip(account, amount, currency, parse_result);
        resolved.tooltip = Some(lsp_types::InlayHintTooltip::MarkupContent(
            lsp_types::MarkupContent {
                kind: lsp_types::MarkupKind::Markdown,
                value: tooltip,
            },
        ));
    }

    resolved
}

/// Build a rich tooltip for an inferred amount hint.
fn build_account_tooltip(
    account: &str,
    inferred_amount: &str,
    currency: &str,
    parse_result: &ParseResult,
) -> String {
    let mut balances: HashMap<String, Decimal> = HashMap::new();
    let mut transaction_count = 0;

    // Calculate running balance for this account
    for spanned in &parse_result.directives {
        if let Directive::Transaction(txn) = &spanned.value {
            for posting in &txn.postings {
                if posting.account.as_ref() == account {
                    transaction_count += 1;
                    if let Some(units) = &posting.units
                        && let Some(number) = units.number()
                    {
                        let curr = units.currency().unwrap_or("???").to_string();
                        *balances.entry(curr).or_default() += number;
                    }
                }
            }
        }
    }

    let mut tooltip = format!("**Inferred:** {} {}\n\n", inferred_amount, currency);
    tooltip.push_str(&format!("**Account:** `{}`\n\n", account));

    if transaction_count > 0 {
        tooltip.push_str(&format!("📊 {} transactions\n\n", transaction_count));

        if !balances.is_empty() {
            tooltip.push_str("**Current Balance:**\n");
            for (curr, amount) in &balances {
                tooltip.push_str(&format!("- {} {}\n", amount, curr));
            }
        }
    } else {
        tooltip.push_str("_First transaction for this account_");
    }

    tooltip
}

#[cfg(test)]
mod tests {
    use super::*;
    use rustledger_parser::parse;

    #[test]
    fn test_inlay_hints_inferred_amount() {
        let source = r#"2024-01-15 * "Coffee Shop"
  Assets:Bank  -5.00 USD
  Expenses:Food
"#;
        let result = parse(source);
        let params = InlayHintParams {
            text_document: lsp_types::TextDocumentIdentifier {
                uri: "file:///test.beancount".parse().unwrap(),
            },
            range: lsp_types::Range {
                start: Position::new(0, 0),
                end: Position::new(3, 0),
            },
            work_done_progress_params: Default::default(),
        };

        let hints = handle_inlay_hints(&params, source, &result);
        assert!(hints.is_some());

        let hints = hints.unwrap();
        assert_eq!(hints.len(), 1);

        // The hint should show the inferred amount (5.00 USD)
        if let InlayHintLabel::String(label) = &hints[0].label {
            assert!(label.contains("5.00"));
            assert!(label.contains("USD"));
        }
    }

    #[test]
    fn test_inlay_hint_resolve() {
        let source = r#"2024-01-15 * "Coffee"
  Assets:Bank  -5.00 USD
  Expenses:Food
2024-01-20 * "Lunch"
  Assets:Bank  -10.00 USD
  Expenses:Food
"#;
        let result = parse(source);

        // Create a hint with data that would be resolved
        let hint = InlayHint {
            position: Position::new(2, 15),
            label: InlayHintLabel::String("  5.00 USD".to_string()),
            kind: Some(InlayHintKind::TYPE),
            text_edits: None,
            tooltip: None,
            padding_left: Some(true),
            padding_right: None,
            data: Some(serde_json::json!({
                "kind": "inferred_amount",
                "account": "Expenses:Food",
                "amount": "5.00",
                "currency": "USD",
            })),
        };

        let resolved = handle_inlay_hint_resolve(hint, &result);

        // Should now have a tooltip
        assert!(resolved.tooltip.is_some());

        if let Some(lsp_types::InlayHintTooltip::MarkupContent(content)) = resolved.tooltip {
            assert!(content.value.contains("Expenses:Food"));
            assert!(content.value.contains("2 transactions"));
        }
    }

    #[test]
    fn test_inlay_hints_disappear_when_amount_explicit() {
        // This test verifies that inlay hints correctly update based on posting.units
        // Issue #491: hints were "lingering" after user typed explicit amount

        // Version 1: Posting WITHOUT amount (should show hint)
        let source_v1 = r#"2024-01-15 * "Paycheck"
  Assets:Bank  5000 USD
  Income:Salary
"#;

        // Version 2: Same posting WITH explicit amount (should NOT show hint)
        let source_v2 = r#"2024-01-15 * "Paycheck"
  Assets:Bank  5000 USD
  Income:Salary  -5000 USD
"#;

        let params = InlayHintParams {
            text_document: lsp_types::TextDocumentIdentifier {
                uri: "file:///test.beancount".parse().unwrap(),
            },
            range: lsp_types::Range {
                start: Position::new(0, 0),
                end: Position::new(10, 0),
            },
            work_done_progress_params: Default::default(),
        };

        // Parse V1 and get hints
        let result_v1 = parse(source_v1);
        let hints_v1 = handle_inlay_hints(&params, source_v1, &result_v1);

        // Parse V2 and get hints
        let result_v2 = parse(source_v2);
        let hints_v2 = handle_inlay_hints(&params, source_v2, &result_v2);

        // V1 should have 1 hint (for Income:Salary without amount)
        assert!(hints_v1.is_some(), "V1 should have hints");
        assert_eq!(
            hints_v1.as_ref().unwrap().len(),
            1,
            "V1 should have exactly 1 hint"
        );

        // V2 should have 0 hints (Income:Salary has explicit amount)
        assert!(
            hints_v2.is_none() || hints_v2.as_ref().unwrap().is_empty(),
            "V2 should have no hints when amount is explicit"
        );

        // This proves server logic is correct.
        // If hints linger in editor after typing, it's a CLIENT issue
        // (client not re-requesting textDocument/inlayHint after didChange)
    }

    /// Regression test for the read-only sibling of #1142.
    ///
    /// Pre-fix, the inferred-amount hint for the amountless posting
    /// landed on the wrong line whenever the prior posting had
    /// `effective_date:` (or any other) metadata between them. With
    /// per-posting span lookup, the hint sits on the posting line
    /// itself.
    #[test]
    fn test_inlay_hint_lands_on_correct_line_with_interleaved_metadata_1142() {
        let source = "\
2024-01-15 * \"Test\"
  Assets:Bank  -5.00 USD
    effective_date: 2024-01-20
  Expenses:Food
";
        let result = parse(source);
        assert!(
            result.errors.is_empty(),
            "parse errors: {:?}",
            result.errors
        );

        let params = InlayHintParams {
            text_document: lsp_types::TextDocumentIdentifier {
                uri: "file:///test.beancount".parse().unwrap(),
            },
            range: lsp_types::Range {
                start: Position::new(0, 0),
                end: Position::new(10, 0),
            },
            work_done_progress_params: Default::default(),
        };

        let hints = handle_inlay_hints(&params, source, &result).unwrap_or_default();
        assert_eq!(hints.len(), 1, "exactly one inferred-amount hint expected");

        // Expenses:Food is on line 3 (after Assets:Bank on line 1 and
        // its metadata on line 2). Pre-fix arithmetic would have put
        // the hint on line 2 (the metadata line).
        assert_eq!(
            hints[0].position.line, 3,
            "inferred-amount hint should be on the posting line, not the metadata line"
        );
    }

    /// Multi-currency transactions used to get NO inferred-amount
    /// hints at all: the bespoke `calculate_inferred_amount` bailed
    /// the moment more than one currency was seen, even when each
    /// currency had exactly one missing posting (a perfectly
    /// inferable case). Delegating to `rustledger_booking::interpolate`
    /// produces a hint per inferred posting, including the
    /// multi-currency case below.
    #[test]
    fn test_inlay_hints_multi_currency_inference() {
        let source = "\
2024-01-15 * \"FX swap\"
  Assets:Bank:USD  100.00 USD
  Assets:Bank:EUR  -90.00 EUR
  Expenses:Fees:USD
  Expenses:Fees:EUR
";
        let result = parse(source);
        assert!(
            result.errors.is_empty(),
            "parse errors: {:?}",
            result.errors
        );

        let params = InlayHintParams {
            text_document: lsp_types::TextDocumentIdentifier {
                uri: "file:///test.beancount".parse().unwrap(),
            },
            range: lsp_types::Range {
                start: Position::new(0, 0),
                end: Position::new(10, 0),
            },
            work_done_progress_params: Default::default(),
        };

        let hints = handle_inlay_hints(&params, source, &result).unwrap_or_default();

        // Both empty postings should get a hint, with the correct
        // per-currency residual. Pre-refactor: zero hints (multi-
        // currency was bailed entirely).
        assert_eq!(
            hints.len(),
            2,
            "expected one hint per inferred posting; got {hints:?}"
        );

        // Labels carry the (sign-flipped) residual + currency. The
        // expected residuals are -100 USD (negating the +100 USD
        // explicit posting) and +90 EUR (negating -90 EUR).
        let labels: Vec<String> = hints
            .iter()
            .map(|h| match &h.label {
                InlayHintLabel::String(s) => s.clone(),
                other => format!("{other:?}"),
            })
            .collect();
        assert!(
            labels
                .iter()
                .any(|l| l.contains("-100") && l.contains("USD")),
            "expected a hint showing -100 USD; got labels = {labels:?}"
        );
        assert!(
            labels.iter().any(|l| l.contains("90") && l.contains("EUR")),
            "expected a hint showing 90 EUR; got labels = {labels:?}"
        );
    }

    /// `NumberOnly`/`CurrencyOnly` source postings already display
    /// one half (the typed digits or the typed currency) on the
    /// posting line. Appending the inferred other-half at line-end
    /// would visually duplicate the typed text or wrongly order
    /// number-then-currency (e.g. `Assets:Cash USD  -50.00 USD`).
    /// The interpolator fills these slots correctly, but the LSP
    /// deliberately suppresses hints for them — the bespoke
    /// pre-refactor implementation only emitted hints for fully-
    /// missing postings, and we preserve that UX.
    #[test]
    fn test_inlay_hints_skip_partial_amounts() {
        // First posting is `CurrencyOnly` ("USD"), second is
        // `NumberOnly` ("-50.00"). The interpolator fills both, but
        // neither should produce a hint.
        let source = "\
2024-01-15 * \"Test\"
  Assets:Bank   50.00 USD
  Expenses:A    USD
  Income:B     -100.00
  Equity:Pad   -50 EUR
  Expenses:Tax  50 EUR
";
        let result = parse(source);
        assert!(
            result.errors.is_empty(),
            "parse errors: {:?}",
            result.errors
        );

        let params = InlayHintParams {
            text_document: lsp_types::TextDocumentIdentifier {
                uri: "file:///test.beancount".parse().unwrap(),
            },
            range: lsp_types::Range {
                start: Position::new(0, 0),
                end: Position::new(20, 0),
            },
            work_done_progress_params: Default::default(),
        };

        let hints = handle_inlay_hints(&params, source, &result);
        assert!(
            hints.is_none() || hints.as_ref().unwrap().is_empty(),
            "no hints expected for partial-amount postings; got {hints:?}"
        );
    }
}
