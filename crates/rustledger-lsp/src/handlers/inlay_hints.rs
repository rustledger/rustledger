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

            // The hint anchors at the end of the account text. We need
            // that column in TWO unit systems and must NOT mix them:
            //   * char columns (`end_col_chars`) to match the
            //     formatter's char-based `number_col`/`number_width`
            //     when computing the visual gap, and
            //   * a source byte offset (`end_col_bytes`) to convert into
            //     an encoding-correct `Position` via `LineIndex` (LSP
            //     `character` is UTF-16 by default; a raw byte count
            //     would misplace the hint on any non-ASCII line).
            // A well-formed fully-missing posting line is
            // `[indent][flag ]account[trailing ws]`, so the end of the
            // trimmed content lands right after the account.
            // Strip a trailing inline comment first: a fully-elided posting line
            // is `[indent][flag ]account[ws][; comment]` with no string or
            // amount before the comment, so the first `;` unambiguously starts
            // it. Without this the hint anchors *past* the comment instead of at
            // the account end.
            let content = line.split_once(';').map_or(line, |(before, _)| before);
            let trimmed = content.trim();
            let indent_bytes = line.len() - line.trim_start().len();
            let end_col_bytes = indent_bytes + trimmed.len();
            let indent_chars = line[..indent_bytes].chars().count();
            let end_col_chars = indent_chars + trimmed.chars().count();

            // Align the greyed-out amount with the column `rledger
            // format` uses for explicit amounts (issue #1346), instead
            // of a fixed 2-space gap. Mirror `emit_posting` EXACTLY: a
            // field pad (account end → `number_col`, clamped to a 2-space
            // minimum) PLUS a separate right-justify pad
            // (`number_width − number_len`). Clamping the *combined* gap
            // instead would shift the number one column left of the
            // explicit amounts whenever a long elided account forces the
            // field pad to its minimum while the justify pad is nonzero.
            // `PostingAlignment::default()` (col 0, width 0) naturally
            // yields the conventional 2-space gap.
            //
            // Caveat: `number_col`/`number_width` are the *canonical*
            // formatter columns (2-space indent, single inner spaces),
            // while `end_col_chars` is measured from the raw source line.
            // So the hint aligns perfectly with explicit amounts only
            // when the file is already formatted (the steady state). On
            // a non-canonically-indented or unformatted line the hint
            // sits where `rledger format` *would* put the amount, which
            // may differ from where the current explicit amount renders.
            let num_text = amount.number.to_string();
            let align = parse_result.alignment;
            let field_pad = align.number_col.saturating_sub(end_col_chars).max(2);
            let justify_pad = align.number_width.saturating_sub(num_text.chars().count());
            let gap = field_pad + justify_pad;
            let label = format!("{}{} {}", " ".repeat(gap), num_text, amount.currency);

            // Encoding-correct anchor: map the UTF-8 byte offset of the
            // account end to a `Position` in the negotiated encoding.
            let Some(line_start_byte) = line_index.position_to_offset(posting_line, 0) else {
                continue;
            };
            let (hint_line, hint_char) =
                line_index.offset_to_position(line_start_byte + end_col_bytes);

            // Store data for resolve - include account for rich tooltip
            let data = serde_json::json!({
                "kind": "inferred_amount",
                "account": source_posting.account.to_string(),
                "amount": amount.number.to_string(),
                "currency": amount.currency.to_string(),
            });

            hints.push(InlayHint {
                position: Position::new(hint_line, hint_char),
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

    /// Compose what a monospace client would actually display: splice
    /// each hint's label into its source line at the hint's character
    /// position. Inlay hints are virtual text, so this reconstructs the
    /// on-screen character grid — the alignment contract the formatter
    /// targets and the thing the user eyeballs in the screenshots.
    ///
    /// (A real client may style inlay text with slightly different pixel
    /// metrics, so this verifies character-grid alignment, not
    /// pixel-exact rendering — but the character grid is the model both
    /// `bean-format` and `rledger format` align to.)
    ///
    /// Test inputs are ASCII, so character index == byte index.
    fn render_with_hints(source: &str, hints: &[InlayHint]) -> Vec<String> {
        let mut lines: Vec<String> = source.lines().map(str::to_string).collect();
        let mut by_line: std::collections::BTreeMap<u32, Vec<&InlayHint>> =
            std::collections::BTreeMap::new();
        for h in hints {
            by_line.entry(h.position.line).or_default().push(h);
        }
        for (line, mut hs) in by_line {
            // Insert right-to-left so earlier splices don't shift the
            // columns of later ones on the same line.
            hs.sort_by_key(|h| std::cmp::Reverse(h.position.character));
            let Some(text) = lines.get_mut(line as usize) else {
                continue;
            };
            for h in hs {
                let InlayHintLabel::String(label) = &h.label else {
                    continue;
                };
                let col = h.position.character as usize;
                let idx = text.char_indices().nth(col).map_or(text.len(), |(i, _)| i);
                text.insert_str(idx, label);
            }
        }
        lines
    }

    /// #1346, the actual visual check: render the hint into the line as a
    /// client would and assert the inferred amount's currency lands in
    /// the SAME column as the explicit amount above it.
    #[test]
    fn test_inlay_hint_renders_aligned_currency_column_1346() {
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

        let rendered = render_with_hints(source, &hints);
        let explicit = &rendered[1]; // `  Expenses:Food:Restaurants  -50.00 USD`
        let hinted = &rendered[2]; // `  Assets:Cash` + hint

        let usd_col = |s: &str| s.find("USD").expect("a USD currency on the line");
        assert_eq!(
            usd_col(explicit),
            usd_col(hinted),
            "currency columns must line up on screen:\n  explicit: {explicit:?}\n  hinted:   {hinted:?}"
        );
        // The right-justified number field also ends at the same column
        // (currency start - 1 space), so the decimals line up too.
        let dot_col = |s: &str| s.find(".00").expect("a .00 on the line");
        assert_eq!(
            dot_col(explicit),
            dot_col(hinted),
            "decimal points must align"
        );
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
        // slot: number_col + (number_width - num_len) — so the number END
        // (and the currency after it) lines up with the explicit amount
        // above. Derive num_len from the hint itself rather than a magic
        // literal, so the assertion survives changes to decimal rendering.
        let label = hint_label(h);
        let leading = label.len() - label.trim_start().len();
        let num_text = label.trim_start().split(' ').next().unwrap();
        let num_len = num_text.chars().count();
        let num_start_col = h.position.character as usize + leading;
        assert_eq!(
            num_start_col,
            align.number_col + align.number_width - num_len,
            "hint number should be right-justified at the formatter column; label={label:?}"
        );
        assert_eq!(label.trim_start(), "50.00 USD");
    }

    #[test]
    fn test_inlay_hint_anchors_before_inline_comment() {
        // The elided posting carries a trailing inline comment. The hint must
        // anchor at the account end (col 13, after `Assets:Cash`), NOT past the
        // `; note here` comment (which the old `line.trim()` swallowed).
        let source = "\
2024-01-15 * \"Test\"
  Expenses:Food  -5.00 USD
  Assets:Cash  ; note here
";
        let result = parse(source);
        assert!(
            result.errors.is_empty(),
            "parse errors: {:?}",
            result.errors
        );
        let params = InlayHintParams {
            text_document: lsp_types::TextDocumentIdentifier {
                uri: "file:///t.beancount".parse().unwrap(),
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
        assert_eq!(h.position.line, 2);
        assert_eq!(
            h.position.character, 13,
            "hint must anchor at the account end (col 13), not past the inline comment"
        );
    }

    /// #1346 regression for the byte-vs-encoding bugs the deep review
    /// surfaced: with a multi-byte account name, (a) `position.character`
    /// must be the UTF-16 column, not the byte length, and (b) the
    /// visual gap must be computed in char columns so the currency still
    /// lines up with the explicit amount above.
    #[test]
    fn test_inlay_hint_nonascii_account_position_and_alignment_1346() {
        // `é` is one char / one UTF-16 unit but two UTF-8 bytes.
        let source = "\
2024-01-15 * \"Test\"
  Expenses:Caféteria  -50.00 USD
  Assets:Café
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
        let h = &hints[0];

        // `  Assets:Café` is 13 chars / 13 UTF-16 units (14 UTF-8 bytes).
        // The anchor must be reported as 13, not the byte length 14.
        assert_eq!(
            h.position.character, 13,
            "position.character must be the UTF-16 column, not the byte length"
        );

        // Rendered on a char grid, the hint's currency must align with
        // the explicit `-50.00 USD` above. (`é` is BMP, so char index ==
        // UTF-16 unit and `render_with_hints` models it faithfully.)
        let rendered = render_with_hints(source, &hints);
        // Char column of `pat` (byte offset → char count; inputs are BMP
        // so the char index is the on-screen grid column).
        let col_of = |s: &str, pat: &str| {
            s.find(pat)
                .map(|b| s[..b].chars().count())
                .expect("pattern present")
        };
        assert_eq!(
            col_of(&rendered[1], "USD"),
            col_of(&rendered[2], "USD"),
            "currency must align on a char grid:\n  {:?}\n  {:?}",
            rendered[1],
            rendered[2]
        );
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

    /// #1346 Finding-1 regression (deep review): when a long elided
    /// account forces the field pad to its 2-space minimum AND the
    /// inferred number is narrower than the field, the justify pad must
    /// still be added on top. Clamping the *combined* gap (the original
    /// bug) put the number one column left of the explicit amounts.
    #[test]
    fn test_inlay_hint_field_and_justify_pad_combine_at_clamp_boundary_1346() {
        // Number-bearing account is short (drives a small number_col);
        // the elided account is long (forces field_pad to the minimum);
        // inferred `100.00` (6) is narrower than width `-100.00` (7), so
        // justify_pad = 1.
        let source = "\
2024-01-15 * \"T\"
  Assets:Bank  -100.00 USD
  Expenses:Groceries:Subcategory:Long
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

        // field_pad = max(2) (clamped) + justify_pad = 1 → 3 spaces.
        // The buggy `gap.max(2)` would have yielded 2.
        let label = hint_label(&hints[0]);
        let leading = label.len() - label.trim_start().len();
        assert_eq!(
            leading, 3,
            "field pad (min 2) + justify pad (1) must combine to 3; label={label:?}"
        );
        assert_eq!(label.trim_start(), "100.00 USD");
    }
}
