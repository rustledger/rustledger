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

use super::utils::{LineIndex, PositionEncoding};

/// Handle an inlay hints request.
pub fn handle_inlay_hints(
    params: &InlayHintParams,
    source: &str,
    parse_result: &ParseResult,
    encoding: PositionEncoding,
) -> Option<Vec<InlayHint>> {
    let range = params.range;
    let mut hints = Vec::new();
    // Build the line index once: O(n) up front, O(log lines) per
    // offset lookup. Without it the per-directive + per-posting
    // lookups below scale quadratically with file size. We also
    // use `line_index.line_text(...)` further down instead of
    // pre-collecting `Vec<&str>` of all lines, so a large fully-
    // explicit ledger pays neither allocation.
    let line_index = LineIndex::new(source, encoding);

    for spanned in &parse_result.directives {
        let Directive::Transaction(txn) = &spanned.value else {
            continue;
        };
        // Skip transactions that fall entirely outside the
        // requested range, in either direction. `span.end` is
        // exclusive (byte after the directive), so an `end_line <
        // range.start.line` test cleanly excludes "directive ended
        // before the visible range started".
        let (start_line, _) = line_index.offset_to_position(spanned.span.start);
        let (end_line, _) = line_index.offset_to_position(spanned.span.end);
        if start_line > range.end.line || end_line < range.start.line {
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
        //    not source-relative. A reachable case is e.g. a
        //    `CurrencyOnly` posting whose currency's residual is
        //    already zero — interpolate fills with 0 and prunes,
        //    shifting later fills. Matching by span — preserved
        //    across `interpolate`'s clone — works regardless of
        //    pruning and shifting.
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
            //
            // Note on the multi-currency single-missing case:
            // `interpolate` fills the source posting with the FIRST
            // residual currency in place, then appends additional
            // posting clones (one per remaining currency, each
            // carrying the SAME span as the template). `find()`
            // returns the in-place fill — so we emit one hint
            // covering only the first currency. Surfacing the
            // others would require either a multi-line hint layout
            // or stacking hints at the same screen position; we
            // accept the single-currency rendering to match the
            // pre-refactor bespoke implementation.
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

            let Some(line) = line_index.line_text(posting_line) else {
                continue;
            };

            // Position the hint at the end of the trimmed line
            // content. We only reach this point for fully-missing
            // source postings (the filter above), so a well-formed
            // posting line is `[indent][flag ]account[trailing ws]`
            // — `indent + trimmed.len()` lands right after the
            // account (or `flag account` if a flag is present),
            // which is where the inferred amount visually belongs.
            let trimmed = line.trim();
            let indent = line.len() - line.trim_start().len();
            let end_col = indent + trimmed.len();

            // Align the greyed-out amount with the column `rledger
            // format` uses for explicit amounts (issue #1346), instead
            // of a fixed 2-space gap that left the hint out of line with
            // sibling amounts. The formatter right-justifies the number
            // in a `number_width` field starting at `number_col`
            // (`ParseResult::alignment`, the same file-wide alignment
            // the parser pre-computed); reproduce that so the hint sits
            // where the real amount would.
            let num_text = amount.number.to_string();
            let align = parse_result.alignment;
            let label = if align.number_col > 0 {
                // Start column of the right-justified number text.
                let num_start =
                    align.number_col + align.number_width.saturating_sub(num_text.chars().count());
                // Gap from the account end to the number, never below
                // the conventional 2-space minimum. A long amount-less
                // account whose end passes `num_start` can't be aligned
                // — the formatter excludes such postings from the column
                // for the same reason (#1346 Option 1 limitation).
                let gap = num_start.saturating_sub(end_col).max(2);
                format!("{}{} {}", " ".repeat(gap), num_text, amount.currency)
            } else {
                // No number-bearing postings to align to: fall back to
                // the conventional 2-space gap.
                format!("  {} {}", num_text, amount.currency)
            };

            // Store data for resolve - include account for rich tooltip
            let data = serde_json::json!({
                "kind": "inferred_amount",
                "account": source_posting.account.to_string(),
                "amount": amount.number.to_string(),
                "currency": amount.currency.to_string(),
            });

            hints.push(InlayHint {
                position: Position::new(posting_line, end_col as u32),
                label: InlayHintLabel::String(label),
                kind: Some(InlayHintKind::TYPE),
                text_edits: None,
                tooltip: None, // Resolved lazily
                // The leading gap is baked into the label so the number
                // lands exactly at the formatter's column; no extra
                // client-side left padding (which would shift it by 1).
                padding_left: Some(false),
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

        let hints = handle_inlay_hints(&params, source, &result, PositionEncoding::Utf16);
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

        // Pattern-match the variant explicitly: a `String` tooltip
        // (the other variant) would silently pass the prior
        // `if let Some(MarkupContent(_))` pattern.
        let content = match resolved.tooltip {
            Some(lsp_types::InlayHintTooltip::MarkupContent(c)) => c,
            other => panic!("expected MarkupContent tooltip; got {other:?}"),
        };
        assert!(content.value.contains("Expenses:Food"));
        assert!(content.value.contains("2 transactions"));
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
        let hints_v1 = handle_inlay_hints(&params, source_v1, &result_v1, PositionEncoding::Utf16);

        // Parse V2 and get hints
        let result_v2 = parse(source_v2);
        let hints_v2 = handle_inlay_hints(&params, source_v2, &result_v2, PositionEncoding::Utf16);

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

        let hints = handle_inlay_hints(&params, source, &result, PositionEncoding::Utf16)
            .unwrap_or_default();
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

        let hints = handle_inlay_hints(&params, source, &result, PositionEncoding::Utf16)
            .unwrap_or_default();

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

    /// `NumberOnly` source postings already display the typed
    /// digits on the posting line. The interpolator can still fill
    /// the currency (e.g., from another posting's units residual),
    /// but appending `  -5000.00 USD` after `-5000.00` would
    /// duplicate the number on screen. The LSP suppresses the
    /// hint; the bespoke pre-refactor implementation did the same.
    ///
    /// This test specifically exercises a transaction where
    /// `interpolate` SUCCEEDS and fills the `NumberOnly` slot —
    /// pinning the filter (not bypass-by-error).
    #[test]
    fn test_inlay_hints_skip_number_only_posting() {
        let source = "\
2024-01-15 * \"Paycheck\"
  Assets:Bank  5000 USD
  Income:Salary  -5000
";
        let result = parse(source);
        assert!(
            result.errors.is_empty(),
            "parse errors: {:?}",
            result.errors
        );

        // Verify the precondition: `interpolate` succeeds and fills
        // the `NumberOnly` slot. Without this, the no-hints assertion
        // below could pass via bypass-by-Err (a non-issue for THIS
        // input, but documenting the requirement).
        let txn = match &result.directives[0].value {
            Directive::Transaction(t) => t,
            _ => unreachable!(),
        };
        let interp = interpolate(txn).expect("interpolate should succeed");
        let salary_posting = interp
            .transaction
            .postings
            .iter()
            .find(|p| p.account.as_ref() == "Income:Salary")
            .expect("Income:Salary should be present after interpolation");
        assert!(
            matches!(&salary_posting.units, Some(IncompleteAmount::Complete(_))),
            "interpolate must have filled NumberOnly to Complete; got {:?}",
            salary_posting.units
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

        let hints = handle_inlay_hints(&params, source, &result, PositionEncoding::Utf16);
        assert!(
            hints.is_none() || hints.as_ref().unwrap().is_empty(),
            "no hint expected for NumberOnly source posting; got {hints:?}"
        );
    }

    /// Same UX invariant as the `NumberOnly` test above, applied to
    /// `CurrencyOnly` (typed `USD`, missing number). Appending the
    /// inferred amount at line-end would render as
    /// `Assets:Cash USD  -50.00 USD` — duplicate currency, wrong
    /// number-then-currency order. The LSP suppresses the hint.
    #[test]
    fn test_inlay_hints_skip_currency_only_posting() {
        let source = "\
2024-01-15 * \"Coffee\"
  Assets:Bank  -5.00 USD
  Expenses:Food USD
";
        let result = parse(source);
        assert!(
            result.errors.is_empty(),
            "parse errors: {:?}",
            result.errors
        );

        // Precondition: interpolate succeeds and fills CurrencyOnly.
        let txn = match &result.directives[0].value {
            Directive::Transaction(t) => t,
            _ => unreachable!(),
        };
        let interp = interpolate(txn).expect("interpolate should succeed");
        let food_posting = interp
            .transaction
            .postings
            .iter()
            .find(|p| p.account.as_ref() == "Expenses:Food")
            .expect("Expenses:Food should be present after interpolation");
        assert!(
            matches!(&food_posting.units, Some(IncompleteAmount::Complete(_))),
            "interpolate must have filled CurrencyOnly to Complete; got {:?}",
            food_posting.units
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

        let hints = handle_inlay_hints(&params, source, &result, PositionEncoding::Utf16);
        assert!(
            hints.is_none() || hints.as_ref().unwrap().is_empty(),
            "no hint expected for CurrencyOnly source posting; got {hints:?}"
        );
    }

    fn hint_label(h: &InlayHint) -> String {
        match &h.label {
            InlayHintLabel::String(s) => s.clone(),
            other => panic!("expected String label; got {other:?}"),
        }
    }

    /// #1346: the inferred-amount hint must align with the column
    /// `rledger format` uses for explicit amounts, not sit at a fixed
    /// 2-space gap after the (short) elided account. Here the explicit
    /// posting has the longer account, so it drives the number column;
    /// the hint on the shorter elided account must be padded out to it.
    #[test]
    fn test_inlay_hint_aligns_with_formatter_amount_column_1346() {
        let source = "\
2024-01-15 * \"Test\"
  Expenses:Food:Restaurants  -50.00 USD
  Assets:Cash
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
        let hints = handle_inlay_hints(&params, source, &result, PositionEncoding::Utf16)
            .unwrap_or_default();
        assert_eq!(hints.len(), 1, "one inferred-amount hint expected");

        let h = &hints[0];
        // Elided `Assets:Cash` is on line 2 (0-indexed).
        assert_eq!(h.position.line, 2);

        let align = result.alignment;
        assert!(align.number_col > 0, "file should have an alignment column");

        // The number text must begin at the formatter's right-justified
        // slot: number_col + (number_width - num_len). With explicit
        // `-50.00` (width 6) and inferred `50.00` (len 5), that is
        // number_col + 1 — so the number END (and the currency after it)
        // lines up with the explicit amount above.
        let label = hint_label(h);
        let leading = label.len() - label.trim_start().len();
        let num_start_col = h.position.character as usize + leading;
        assert_eq!(
            num_start_col,
            align.number_col + align.number_width - 5,
            "hint number should be right-justified at the formatter column; label={label:?}"
        );
        assert_eq!(label.trim_start(), "50.00 USD");
    }

    /// #1346 Option-1 limitation: when the *elided* posting has the
    /// longest account, the formatter excludes it from the number
    /// column, so the hint can't be aligned — it falls back to the
    /// conventional 2-space gap rather than overlapping the account.
    #[test]
    fn test_inlay_hint_long_elided_account_falls_back_to_min_gap_1346() {
        let source = "\
2024-01-15 * \"Opening\"
  Assets:Checking  1000.00 USD
  Equity:Opening-Balances
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
        let hints = handle_inlay_hints(&params, source, &result, PositionEncoding::Utf16)
            .unwrap_or_default();
        assert_eq!(hints.len(), 1);

        // `Equity:Opening-Balances` ends past the number column, so the
        // gap clamps to the 2-space minimum.
        let label = hint_label(&hints[0]);
        let leading = label.len() - label.trim_start().len();
        assert_eq!(leading, 2, "expected min 2-space gap; label={label:?}");
        assert_eq!(label.trim_start(), "-1000.00 USD");
    }
}
