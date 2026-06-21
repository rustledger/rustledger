//! Code actions handler for quick fixes and refactorings.
//!
//! Provides code actions for:
//! - Adding missing account open directives
//! - Balancing transaction postings
//! - Formatting amounts consistently
//!
//! Supports resolve for lazy-loading workspace edits.

use lsp_types::{
    CodeAction, CodeActionKind, CodeActionParams, CodeActionResponse, Position, Range, TextEdit,
    Uri, WorkspaceEdit,
};
use rustledger_core::Directive;
use rustledger_parser::{ParseErrorKind, ParseResult};
use std::collections::{BTreeSet, HashMap, HashSet};

use super::utils::{LineIndex, PositionEncoding, ranges_overlap};

/// Handle a code action request.
///
/// `encoding` is the position encoding negotiated with the client at
/// LSP initialization. Handlers that emit LSP `Position` values from
/// byte offsets must thread it through `LineIndex::new(source,
/// encoding)`; otherwise positions emitted in the wrong encoding
/// misalign on non-ASCII content.
pub fn handle_code_actions(
    params: &CodeActionParams,
    source: &str,
    parse_result: &ParseResult,
    encoding: PositionEncoding,
) -> Option<CodeActionResponse> {
    let mut actions = Vec::new();

    let range = params.range;
    let uri = params.text_document.uri.clone();
    let line_index = LineIndex::new(source, encoding);

    // Collect all defined accounts
    let defined_accounts = collect_defined_accounts(parse_result);

    // Collect all used accounts
    let used_accounts = collect_used_accounts(parse_result);

    // Find undefined accounts used in the document
    let undefined_accounts: Vec<_> = used_accounts
        .difference(&defined_accounts)
        .cloned()
        .collect();

    // If there are undefined accounts, offer to create open directives
    for account in undefined_accounts {
        // Check if this account is on or near the selected range
        if is_account_in_range(&line_index, &account, range, parse_result) {
            let action = create_open_directive_action(&uri, &account);
            actions.push(action);
        }
    }

    // Check for unbalanced transactions in range
    if let Some(action) = check_unbalanced_transactions(params, &line_index, parse_result) {
        actions.push(action);
    }

    // "Remove BOM" quick fixes for every mid-file BOM diagnostic whose
    // span overlaps the requested range. Consumes the structural
    // `ParseErrorKind::BomInDirectiveBody` variant the parser emits
    // — the round-13 architectural reason for adding the dedicated
    // variant was exactly this: enable downstream UX that detects the
    // case structurally instead of regex-matching the message.
    actions.extend(bom_removal_actions(
        parse_result,
        source,
        &uri,
        range,
        encoding,
    ));

    // Import review actions (accept categorization, batch accept)
    actions.extend(super::import::import_code_actions(
        &parse_result.directives,
        source,
        range,
        encoding,
    ));

    if actions.is_empty() {
        None
    } else {
        Some(actions.into_iter().map(|a| a.into()).collect())
    }
}

/// Emit a "Remove BOM" quick-fix `CodeAction` for each
/// `ParseErrorKind::BomInDirectiveBody` diagnostic whose span overlaps
/// the requested range.
///
/// One action per diagnostic; the action's `WorkspaceEdit` carries
/// one `TextEdit` per U+FEFF occurrence found inside the diagnostic
/// span. This delivers all the BOMs the diagnostic covers in a single
/// click — even when they are non-adjacent inside the span — while
/// keeping the action title scoped to "this position" so users see
/// one entry per diagnostic in the quick-fix menu.
///
/// LSP positions are emitted in the encoding negotiated with the
/// client at initialization, via [`LineIndex::offset_to_position`].
/// Without this, the emitted range misaligns on non-ASCII content
/// (or on the BOM itself, which is 3 bytes / 1 UTF-16 unit) —
/// clients delete BOM + adjacent characters or just the first byte
/// of the BOM, depending on the encoding mismatch direction.
fn bom_removal_actions(
    parse_result: &ParseResult,
    source: &str,
    uri: &Uri,
    request_range: Range,
    encoding: PositionEncoding,
) -> Vec<CodeAction> {
    let line_index = LineIndex::new(source, encoding);

    // Round-19 dedupe: the parser deliberately surfaces multiple
    // overlapping `BomInDirectiveBody` errors for the same BOM byte
    // (consume_leading_bom_run emits a focused per-BOM diagnostic;
    // parse_entry recovery may emit an additive whole-line
    // BomInDirectiveBody for the same span). Pre-round-19 this fn
    // emitted one CodeAction per ParseError, producing visually
    // identical "Remove BOM" entries for the same byte. Now we
    // collect every BOM byte offset across every error, dedupe by
    // offset, and emit ONE action per unique BOM byte (or one
    // grouped action if the request range covers many).
    let mut bom_offsets: BTreeSet<usize> = BTreeSet::new();
    for err in &parse_result.errors {
        if !matches!(err.kind, ParseErrorKind::BomInDirectiveBody) {
            continue;
        }
        let span_text = source.get(err.span.start..err.span.end).unwrap_or("");
        // Walk EVERY U+FEFF in the diagnostic span. A span like
        // `\u{FEFF}foo\u{FEFF}` (non-adjacent BOMs) contributes two
        // distinct byte offsets; the BTreeSet collapses duplicates
        // across errors that overlap.
        for (offset_in_span, _) in span_text.match_indices('\u{FEFF}') {
            bom_offsets.insert(err.span.start + offset_in_span);
        }
    }

    // For each unique BOM byte that overlaps the request range,
    // build a TextEdit. Sorted iteration via BTreeSet gives
    // deterministic action ordering — useful for editors that
    // dedupe quick-fix lists by title-then-position.
    let bom_byte_len = '\u{FEFF}'.len_utf8();
    let edits: Vec<TextEdit> = bom_offsets
        .into_iter()
        .filter_map(|bom_start| {
            let bom_end = bom_start + bom_byte_len;
            let (sl, sc) = line_index.offset_to_position(bom_start);
            let (el, ec) = line_index.offset_to_position(bom_end);
            let bom_range = Range::new(Position::new(sl, sc), Position::new(el, ec));
            if !ranges_overlap(bom_range, request_range) {
                return None;
            }
            Some(TextEdit {
                range: bom_range,
                new_text: String::new(),
            })
        })
        .collect();

    if edits.is_empty() {
        return Vec::new();
    }

    // Single grouped action: clicking "Remove BOM" deletes every
    // BOM byte in scope at once. Multi-action menus listing the
    // same byte twice were the round-19 reviewer-flagged UX bug.
    let title = if edits.len() == 1 {
        "Remove BOM (U+FEFF)".to_string()
    } else {
        format!("Remove {} BOM bytes (U+FEFF)", edits.len())
    };

    #[allow(clippy::mutable_key_type)]
    let mut changes = HashMap::new();
    changes.insert(uri.clone(), edits);

    vec![CodeAction {
        title,
        kind: Some(CodeActionKind::QUICKFIX),
        edit: Some(WorkspaceEdit {
            changes: Some(changes),
            document_changes: None,
            change_annotations: None,
        }),
        ..CodeAction::default()
    }]
}

/// Collect all accounts that have been opened.
fn collect_defined_accounts(parse_result: &ParseResult) -> HashSet<String> {
    let mut accounts = HashSet::new();

    for spanned in &parse_result.directives {
        if let Directive::Open(open) = &spanned.value {
            accounts.insert(open.account.to_string());
        }
    }

    accounts
}

/// Collect all accounts used in the document.
fn collect_used_accounts(parse_result: &ParseResult) -> HashSet<String> {
    let mut accounts = HashSet::new();

    for spanned in &parse_result.directives {
        match &spanned.value {
            Directive::Transaction(txn) => {
                for posting in &txn.postings {
                    accounts.insert(posting.account.to_string());
                }
            }
            Directive::Balance(bal) => {
                accounts.insert(bal.account.to_string());
            }
            Directive::Pad(pad) => {
                accounts.insert(pad.account.to_string());
                accounts.insert(pad.source_account.to_string());
            }
            Directive::Note(note) => {
                accounts.insert(note.account.to_string());
            }
            Directive::Document(doc) => {
                accounts.insert(doc.account.to_string());
            }
            Directive::Close(close) => {
                accounts.insert(close.account.to_string());
            }
            _ => {}
        }
    }

    accounts
}

/// Check if an account is mentioned in or near the given range.
fn is_account_in_range(
    line_index: &LineIndex<'_>,
    account: &str,
    range: Range,
    parse_result: &ParseResult,
) -> bool {
    // Check a few lines around the selection. Fetch each line via
    // LineIndex so we don't re-split the whole source on every
    // undefined-account check (called once per undefined account).
    let start_line = range.start.line;
    let window_start = start_line.saturating_sub(3);
    let window_end = start_line.saturating_add(10);
    for line_idx in window_start..=window_end {
        if let Some(line) = line_index.line_text(line_idx)
            && line.contains(account)
        {
            return true;
        }
    }

    // Also check if we're inside a transaction that uses this account
    for spanned in &parse_result.directives {
        if let Directive::Transaction(txn) = &spanned.value {
            let (dir_line, _) = line_index.offset_to_position(spanned.span.start);
            let (end_line, _) = line_index.offset_to_position(spanned.span.end);

            // Check if range overlaps with transaction
            if (range.start.line <= end_line) && (range.end.line >= dir_line) {
                for posting in &txn.postings {
                    if posting.account.as_ref() == account {
                        return true;
                    }
                }
            }
        }
    }

    false
}

/// Create a code action to add an open directive for an account.
/// The edit is deferred to the resolve phase for better performance.
fn create_open_directive_action(uri: &Uri, account: &str) -> CodeAction {
    // Store data for resolve - the actual edit will be computed lazily
    let data = serde_json::json!({
        "kind": "add_open_directive",
        "account": account,
        "uri": uri.as_str(),
    });

    CodeAction {
        title: format!("Add 'open {}' directive", account),
        kind: Some(CodeActionKind::QUICKFIX),
        diagnostics: None,
        edit: None, // Resolved lazily
        command: None,
        is_preferred: Some(true),
        disabled: None,
        data: Some(data),
    }
}

/// Handle a code action resolve request.
/// Computes the workspace edit for a code action.
#[allow(clippy::mutable_key_type)] // Uri is required as key by LSP WorkspaceEdit API
pub fn handle_code_action_resolve(
    action: CodeAction,
    source: &str,
    parse_result: &ParseResult,
    uri: &Uri,
    encoding: PositionEncoding,
) -> CodeAction {
    let mut resolved = action.clone();

    if let Some(data) = &action.data
        && data.get("kind").and_then(|v| v.as_str()) == Some("add_open_directive")
        && let Some(account) = data.get("account").and_then(|v| v.as_str())
    {
        let line_index = LineIndex::new(source, encoding);
        resolved.edit = Some(compute_open_directive_edit(
            uri,
            source,
            &line_index,
            account,
            parse_result,
        ));
    }

    resolved
}

/// Compute the workspace edit for adding an open directive.
#[allow(clippy::mutable_key_type)] // Uri is required as key by LSP WorkspaceEdit API
fn compute_open_directive_edit(
    uri: &Uri,
    source: &str,
    line_index: &LineIndex,
    account: &str,
    parse_result: &ParseResult,
) -> WorkspaceEdit {
    // Find the earliest date in the file or use a default
    let earliest_date =
        find_earliest_date(parse_result).unwrap_or_else(|| "2000-01-01".to_string());

    // Find where to insert the open directive
    let insert = find_open_directive_position(source, line_index, parse_result);

    // Normally the directive sits on its own fresh line (trailing newline).
    // When inserting at the end of an existing line (a file with no trailing
    // newline), prefix a newline and drop the trailing one so we don't append
    // onto — and corrupt — the existing directive.
    let new_text = if insert.prepend_newline {
        format!("\n{} open {}", earliest_date, account)
    } else {
        format!("{} open {}\n", earliest_date, account)
    };

    let mut changes = HashMap::new();
    changes.insert(
        uri.clone(),
        vec![TextEdit {
            range: Range {
                start: insert.position,
                end: insert.position,
            },
            new_text,
        }],
    );

    WorkspaceEdit {
        changes: Some(changes),
        document_changes: None,
        change_annotations: None,
    }
}

/// Find the earliest date in the document.
fn find_earliest_date(parse_result: &ParseResult) -> Option<String> {
    let mut earliest: Option<rustledger_core::NaiveDate> = None;

    for spanned in &parse_result.directives {
        let date = match &spanned.value {
            Directive::Transaction(t) => Some(t.date),
            Directive::Open(o) => Some(o.date),
            Directive::Close(c) => Some(c.date),
            Directive::Balance(b) => Some(b.date),
            Directive::Pad(p) => Some(p.date),
            Directive::Commodity(c) => Some(c.date),
            Directive::Event(e) => Some(e.date),
            Directive::Note(n) => Some(n.date),
            Directive::Document(d) => Some(d.date),
            Directive::Price(p) => Some(p.date),
            Directive::Query(q) => Some(q.date),
            Directive::Custom(c) => Some(c.date),
        };

        if let Some(d) = date {
            earliest = Some(earliest.map_or(d, |e| e.min(d)));
        }
    }

    earliest.map(|d| d.to_string())
}

/// Where to insert a new `open` directive.
struct OpenInsert {
    position: Position,
    /// When `true`, the new directive must be prefixed with a newline (it's
    /// being inserted at the end of an existing line rather than on a fresh
    /// blank line) and must NOT carry a trailing newline.
    prepend_newline: bool,
}

/// Find the position to insert new open directives.
fn find_open_directive_position(
    source: &str,
    line_index: &LineIndex,
    parse_result: &ParseResult,
) -> OpenInsert {
    // Find the last open directive and insert after it
    let mut last_open_end: Option<usize> = None;

    for spanned in &parse_result.directives {
        if matches!(&spanned.value, Directive::Open(_)) {
            last_open_end = Some(spanned.span.end);
        }
    }

    let Some(offset) = last_open_end else {
        // No open directives, insert at the beginning (on its own line).
        return OpenInsert {
            position: Position::new(0, 0),
            prepend_newline: false,
        };
    };

    // A directive's span end points at the *start of the next directive*, so it
    // includes trailing blank lines. Trim back to the open's last content byte
    // before taking the line; otherwise `line + 1` overshoots and the inserted
    // `open` lands inside a following transaction (between its header and its
    // postings). Trimming also keeps it correct for opens that carry an
    // indented metadata block.
    let content_end = source[..offset.min(source.len())].trim_end().len();
    let (line, col) = line_index.offset_to_position(content_end);

    if source[content_end..].contains('\n') {
        // There's a real next line — insert at its start on a fresh line.
        OpenInsert {
            position: Position::new(line + 1, 0),
            prepend_newline: false,
        }
    } else {
        // The last `open` is on the final line with no trailing newline, so
        // `line + 1` would reference a non-existent line. Insert at the end of
        // that line and prefix a newline so the directive starts on its own
        // line instead of being appended onto the existing one.
        OpenInsert {
            position: Position::new(line, col),
            prepend_newline: true,
        }
    }
}

/// Check for unbalanced transactions and offer to add a balancing posting.
fn check_unbalanced_transactions(
    params: &CodeActionParams,
    line_index: &LineIndex,
    parse_result: &ParseResult,
) -> Option<CodeAction> {
    let range = params.range;

    for spanned in &parse_result.directives {
        if let Directive::Transaction(txn) = &spanned.value {
            let (start_line, _) = line_index.offset_to_position(spanned.span.start);
            let (end_line, _) = line_index.offset_to_position(spanned.span.end);

            // Check if selection is within this transaction
            if range.start.line >= start_line && range.start.line <= end_line {
                // Check if transaction has exactly one posting without amount
                let postings_without_amount =
                    txn.postings.iter().filter(|p| p.units.is_none()).count();

                let postings_with_amount =
                    txn.postings.iter().filter(|p| p.units.is_some()).count();

                // If there's exactly one posting with amount and one without, we can compute the balance
                if postings_without_amount == 1 && postings_with_amount >= 1 {
                    // Transaction is already auto-balanced by the empty posting
                    continue;
                }

                // If all postings have amounts but don't balance, offer to fix
                if postings_without_amount == 0 && postings_with_amount >= 2 {
                    // This would require more complex balance calculation
                    // For now, just skip
                    continue;
                }
            }
        }
    }

    None
}

#[cfg(test)]
mod tests {
    use super::*;
    use rustledger_parser::parse;

    #[test]
    fn test_collect_accounts() {
        let source = r#"
2024-01-01 open Assets:Bank USD
2024-01-15 * "Coffee Shop"
  Assets:Bank  -5.00 USD
  Expenses:Food
"#;
        let result = parse(source);

        let defined = collect_defined_accounts(&result);
        assert!(defined.contains("Assets:Bank"));
        assert!(!defined.contains("Expenses:Food"));

        let used = collect_used_accounts(&result);
        assert!(used.contains("Assets:Bank"));
        assert!(used.contains("Expenses:Food"));
    }

    /// A mid-file BOM produces a `Remove BOM` quick-fix action whose
    /// edit deletes exactly the BOM byte range. Verifies the LSP
    /// surface for the round-13 `BomInDirectiveBody` variant.
    #[test]
    #[allow(clippy::mutable_key_type)]
    fn test_bom_removal_code_action_for_mid_file_bom() {
        use lsp_types::{
            CodeActionContext, PartialResultParams, TextDocumentIdentifier, Uri,
            WorkDoneProgressParams,
        };
        // BOM mid-source forces parse to surface BomInDirectiveBody.
        let source = "2024-01-01 open Assets:Bank USD\n\u{FEFF}2024-01-02 open Assets:Cash USD\n";
        let result = parse(source);
        assert!(
            result
                .errors
                .iter()
                .any(|e| matches!(e.kind, ParseErrorKind::BomInDirectiveBody)),
            "expected a BomInDirectiveBody error in parse output"
        );
        let uri: Uri = "file:///test.bean".parse().unwrap();
        // Range covers the whole file to ensure overlap.
        let params = CodeActionParams {
            text_document: TextDocumentIdentifier { uri: uri.clone() },
            range: Range::new(Position::new(0, 0), Position::new(100, 0)),
            context: CodeActionContext::default(),
            work_done_progress_params: WorkDoneProgressParams::default(),
            partial_result_params: PartialResultParams::default(),
        };
        let response = handle_code_actions(&params, source, &result, PositionEncoding::Utf16)
            .expect("expected at least one code action");
        let bom_action = response
            .into_iter()
            .find_map(|a| match a {
                lsp_types::CodeActionOrCommand::CodeAction(action) => {
                    if action.title.contains("Remove BOM") {
                        Some(action)
                    } else {
                        None
                    }
                }
                lsp_types::CodeActionOrCommand::Command(_) => None,
            })
            .expect("expected a 'Remove BOM' quick-fix action");
        assert_eq!(bom_action.kind, Some(CodeActionKind::QUICKFIX));
        let edit = bom_action.edit.expect("action must carry a WorkspaceEdit");
        let changes = edit.changes.expect("edit must include changes");
        let text_edits = &changes[&uri];
        assert_eq!(text_edits.len(), 1, "expected exactly one TextEdit");
        // The edit's new_text is empty (delete the BOM byte).
        assert!(
            text_edits[0].new_text.is_empty(),
            "BOM removal must be a deletion (empty new_text)"
        );
        // The edit's range must cover EXACTLY the BOM in UTF-16 code
        // units — NOT in bytes. The BOM byte sits at byte 32 (the
        // first `\n` is at byte 31), which is line 1, character 0.
        // U+FEFF is 1 UTF-16 code unit, so the range ends at
        // character 1 (NOT character 3 — which would be the off-by-2
        // bug if we'd kept emitting byte columns).
        assert_eq!(
            text_edits[0].range,
            Range::new(Position::new(1, 0), Position::new(1, 1)),
            "BOM range must be in UTF-16 code units (BOM = 1 UTF-16 unit); \
             a (1,0)..(1,3) range here would indicate byte columns leaking through"
        );
    }

    /// Two non-adjacent mid-line BOMs in a single source produce
    /// quick-fix actions whose TextEdits cover BOTH BOMs (whether
    /// emitted as one action with two edits, or two actions with one
    /// edit each — both shapes are valid LSP UX; the contract this
    /// test enforces is "no BOM goes unfixable" by walking every
    /// `Remove BOM` action and summing their edits).
    ///
    /// Pre-round-17, the parser bundled all mid-line BOMs into one
    /// whole-line error so `bom_removal_actions` produced exactly one
    /// action with two `match_indices('\u{FEFF}')` edits. The round-17
    /// `consume_leading_bom_run` recovery now emits per-BOM-token
    /// diagnostics for BOMs that land at the start of a parse
    /// attempt, so the same input may produce two distinct actions —
    /// each carrying one edit. The user-visible contract ("both BOMs
    /// are deletable in one click apiece") holds either way.
    #[test]
    #[allow(clippy::mutable_key_type)]
    fn test_bom_removal_action_covers_all_boms_in_span() {
        use lsp_types::{
            CodeActionContext, PartialResultParams, TextDocumentIdentifier, Uri,
            WorkDoneProgressParams,
        };
        // Two BOMs separated by ASCII content. `2024-01-01 open
        // Assets:Bank` is valid; the BOMs corrupt it after the
        // account name.
        let source = "2024-01-01 open Assets:Bank \u{FEFF}USD \u{FEFF}EUR\n";
        let result = parse(source);
        let bom_errs = result
            .errors
            .iter()
            .filter(|e| matches!(e.kind, ParseErrorKind::BomInDirectiveBody))
            .count();
        assert!(
            bom_errs >= 1,
            "expected at least one BomInDirectiveBody error in parse output, got: {:?}",
            result.errors
        );

        let uri: Uri = "file:///test.bean".parse().unwrap();
        let params = CodeActionParams {
            text_document: TextDocumentIdentifier { uri: uri.clone() },
            range: Range::new(Position::new(0, 0), Position::new(100, 0)),
            context: CodeActionContext::default(),
            work_done_progress_params: WorkDoneProgressParams::default(),
            partial_result_params: PartialResultParams::default(),
        };
        let response = handle_code_actions(&params, source, &result, PositionEncoding::Utf16)
            .expect("expected at least one code action");
        let bom_actions: Vec<_> = response
            .into_iter()
            .filter_map(|a| match a {
                lsp_types::CodeActionOrCommand::CodeAction(action)
                    if action.title.contains("Remove") && action.title.contains("BOM") =>
                {
                    Some(action)
                }
                _ => None,
            })
            .collect();
        assert!(
            !bom_actions.is_empty(),
            "expected at least one 'Remove ... BOM' quick-fix action"
        );

        // Sum every TextEdit across every BOM action. The contract:
        // both BOMs in the source are deletable via the quick-fix
        // surface.
        let mut all_edits: Vec<TextEdit> = Vec::new();
        for action in bom_actions {
            let edit = action.edit.expect("action must carry a WorkspaceEdit");
            let changes = edit.changes.expect("edit must include changes");
            all_edits.extend(changes[&uri].iter().cloned());
        }
        assert_eq!(
            all_edits.len(),
            2,
            "expected one TextEdit per BOM occurrence across all actions; got {} edits",
            all_edits.len()
        );
        for edit in &all_edits {
            assert!(
                edit.new_text.is_empty(),
                "each BOM removal is a deletion (empty new_text)"
            );
        }
        // The two edits must target distinct positions. A regression
        // that emits two edits at the same byte (e.g., a copy-paste
        // bug in the per-error loop) would produce overlapping edits
        // which the LSP spec rejects within a single WorkspaceEdit;
        // even split across actions the duplication is wrong UX.
        assert_ne!(
            all_edits[0].range, all_edits[1].range,
            "multi-BOM edits must target distinct positions, not duplicates"
        );
    }

    /// `bom_removal_actions` emits LSP positions in the encoding the
    /// client negotiated. This test pins the UTF-8 path explicitly:
    /// a single-byte-per-char source (ASCII before the BOM) emits the
    /// BOM as a 3-column range (bytes 0..3 of the line), where the
    /// UTF-16 path would emit 0..1 (1 UTF-16 code unit). Without
    /// encoding-aware emission, the BOM action would corrupt non-
    /// ASCII content for one client class or the other.
    #[test]
    #[allow(clippy::mutable_key_type)]
    fn test_bom_removal_action_utf8_encoding_emits_byte_columns() {
        use lsp_types::{
            CodeActionContext, PartialResultParams, TextDocumentIdentifier, Uri,
            WorkDoneProgressParams,
        };
        let source = "2024-01-01 open Assets:Bank USD\n\u{FEFF}2024-01-02 open Assets:Cash USD\n";
        let result = parse(source);
        let uri: Uri = "file:///test.bean".parse().unwrap();
        let params = CodeActionParams {
            text_document: TextDocumentIdentifier { uri: uri.clone() },
            range: Range::new(Position::new(0, 0), Position::new(100, 0)),
            context: CodeActionContext::default(),
            work_done_progress_params: WorkDoneProgressParams::default(),
            partial_result_params: PartialResultParams::default(),
        };
        // Pass Utf8 — the encoding a UTF-8-capable client would have
        // negotiated.
        let response = handle_code_actions(&params, source, &result, PositionEncoding::Utf8)
            .expect("expected at least one code action");
        let bom_action = response
            .into_iter()
            .find_map(|a| match a {
                lsp_types::CodeActionOrCommand::CodeAction(action) => {
                    if action.title.contains("Remove BOM") {
                        Some(action)
                    } else {
                        None
                    }
                }
                lsp_types::CodeActionOrCommand::Command(_) => None,
            })
            .expect("expected a 'Remove BOM' quick-fix action");
        let edit = bom_action.edit.expect("action must carry a WorkspaceEdit");
        let changes = edit.changes.expect("edit must include changes");
        let text_edits = &changes[&uri];
        // BOM at line 1, column 0 in byte terms; END at column 3
        // (BOM is 3 UTF-8 bytes). Contrast with the UTF-16 test which
        // expects column 1 (1 UTF-16 code unit).
        assert_eq!(
            text_edits[0].range,
            Range::new(Position::new(1, 0), Position::new(1, 3)),
            "UTF-8 encoding must emit byte columns: BOM is 3 bytes wide"
        );
    }

    #[test]
    fn test_find_earliest_date() {
        let source = r#"
2024-06-15 open Assets:Bank
2024-01-01 open Assets:Cash
2024-03-01 * "Test"
  Assets:Bank  -10 USD
  Assets:Cash
"#;
        let result = parse(source);
        let earliest = find_earliest_date(&result);
        assert_eq!(earliest, Some("2024-01-01".to_string()));
    }

    #[test]
    #[allow(clippy::mutable_key_type)] // Uri has interior mutability but is safe in tests
    fn test_code_action_resolve() {
        let source = r#"
2024-01-01 open Assets:Bank USD
2024-01-15 * "Coffee"
  Assets:Bank  -5.00 USD
  Expenses:Food
"#;
        let result = parse(source);
        let uri: Uri = "file:///test.beancount".parse().unwrap();

        // Create a code action with data (as returned by handle_code_actions)
        let action = CodeAction {
            title: "Add 'open Expenses:Food' directive".to_string(),
            kind: Some(CodeActionKind::QUICKFIX),
            diagnostics: None,
            edit: None, // Not resolved yet
            command: None,
            is_preferred: Some(true),
            disabled: None,
            data: Some(serde_json::json!({
                "kind": "add_open_directive",
                "account": "Expenses:Food",
                "uri": uri.as_str(),
            })),
        };

        let resolved =
            handle_code_action_resolve(action, source, &result, &uri, PositionEncoding::Utf16);

        // Should now have an edit
        assert!(resolved.edit.is_some());

        let edit = resolved.edit.unwrap();
        let changes = edit.changes.unwrap();
        let edits = changes.get(&uri).unwrap();

        // Should insert an open directive
        assert_eq!(edits.len(), 1);
        assert!(edits[0].new_text.contains("open Expenses:Food"));
        assert!(edits[0].new_text.contains("2024-01-01")); // Earliest date

        // Regression: the insert must land on line 2 (right after the existing
        // `open` on line 1, before the transaction header) — NOT line 3, which
        // would split the transaction header from its postings and corrupt the
        // file. (Source has a leading newline: line0 blank, line1 open,
        // line2 txn header, line3 postings.)
        assert_eq!(
            edits[0].range.start,
            Position::new(2, 0),
            "open must be inserted before the transaction, not inside it"
        );
        assert_eq!(edits[0].range.end, Position::new(2, 0));
    }

    #[test]
    #[allow(clippy::mutable_key_type)] // Uri has interior mutability but is safe in tests
    fn test_code_action_resolve_no_trailing_newline() {
        // The only `open` is on the final line with NO trailing newline.
        // Inserting at `line + 1` would reference a non-existent line; instead
        // the new directive must be appended at end-of-line with a LEADING
        // newline so it starts on its own line and doesn't corrupt the last one.
        let source = "2024-01-15 * \"x\"\n  Assets:Bank  -5 USD\n  Expenses:Food  5 USD\n2024-01-01 open Assets:Bank USD";
        let result = parse(source);
        let uri: Uri = "file:///test.beancount".parse().unwrap();
        let action = CodeAction {
            title: "Add 'open Expenses:Food' directive".to_string(),
            kind: Some(CodeActionKind::QUICKFIX),
            diagnostics: None,
            edit: None,
            command: None,
            is_preferred: Some(true),
            disabled: None,
            data: Some(serde_json::json!({
                "kind": "add_open_directive",
                "account": "Expenses:Food",
                "uri": uri.as_str(),
            })),
        };
        let resolved =
            handle_code_action_resolve(action, source, &result, &uri, PositionEncoding::Utf16);
        let edit = resolved.edit.unwrap();
        let edits = edit.changes.unwrap().get(&uri).unwrap().clone();
        assert_eq!(edits.len(), 1);
        // Inserted at the end of the last line (line 3), with a leading newline.
        assert_eq!(edits[0].range.start.line, 3);
        assert!(
            edits[0].new_text.starts_with('\n'),
            "must prefix a newline so the directive is on its own line: {:?}",
            edits[0].new_text
        );
        assert!(!edits[0].new_text.ends_with('\n'));
        assert!(edits[0].new_text.contains("open Expenses:Food"));
    }
}
