//! LSP protocol-level integration tests.
//!
//! See `tests/lsp_protocol/harness.rs` (module-level rustdoc) for
//! the rationale, layering, and supported-client contract. The
//! short version: these tests drive a freshly-spawned rledger-lsp
//! over an in-process `Connection::memory()` channel pair and assert
//! on full LSP message flows. They catch the protocol-interaction
//! bugs that handler-level tests structurally cannot.

#[path = "lsp_protocol/harness.rs"]
mod harness;
#[path = "lsp_protocol/quirks.rs"]
mod quirks;

use std::time::{Duration, Instant};

use harness::{LspTestClient, test_uri};
use lsp_types::request::{CodeLensRequest, CodeLensResolve, SemanticTokensFullRequest};
use lsp_types::{CodeLensParams, SemanticTokensParams, TextDocumentIdentifier};

/// Smoke test: spawn the harness, perform initialize, send a
/// `textDocument/codeLens` request, get a response. If this test
/// fails the harness itself is broken; every other test in this
/// binary builds on it.
#[test]
fn harness_smoke_initialize_and_codelens() {
    let mut client = LspTestClient::spawn();
    client.initialize();

    let uri = test_uri("smoke.beancount");
    client.open_document(&uri, "2024-01-01 open Assets:Bank USD\n");

    let lenses: Option<Vec<lsp_types::CodeLens>> =
        client.request::<CodeLensRequest>(CodeLensParams {
            text_document: TextDocumentIdentifier {
                uri: uri.parse().unwrap(),
            },
            work_done_progress_params: Default::default(),
            partial_result_params: Default::default(),
        });

    let lenses = lenses.expect("codeLens returned Some on a non-empty document");
    assert!(
        !lenses.is_empty(),
        "open directive should produce at least one lens"
    );
}

/// Regression for issue #1253: a balance assertion must ship with
/// its final ✓ / ⚠ title on the *initial* `textDocument/codeLens`
/// response, with no `data` payload that would require a
/// `codeLens/resolve` round-trip. That structural invariant is what
/// closes the exposure to nvim's resolve-cancellation race: with no
/// resolve round-trip, there is nothing for the cancel to discard.
///
/// Note on what this test does NOT exercise: `textDocument/codeLens`
/// is synchronously dispatched on the main loop
/// (`main_loop::try_dispatch_async` only async-dispatches
/// `codeLens/resolve` and `semanticTokens/full`), so the server
/// processes the request to completion before it ever reads the
/// `$/cancelRequest` notification we fire after it. The cancel is
/// sent anyway, as belt-and-braces: if a future refactor moves
/// codeLens into async dispatch, the cancel would then actually race
/// the response. The substantive assertions are the lens-shape
/// invariants (✓ title, no `data`), which hold regardless of whether
/// the cancel "won" the race.
#[test]
fn issue_1253_balance_lens_ships_eagerly_resolved_with_cancel_belt_and_braces() {
    let mut client = LspTestClient::spawn();
    client.initialize();

    let uri = test_uri("issue_1253.beancount");
    client.open_document(
        &uri,
        "2012-01-01 open Assets:Bank\n\
         2012-01-01 open Income:Employment\n\
         \n\
         2012-02-01 * \"Salary\"\n  \
           Assets:Bank                   1000 USD\n  \
           Income:Employment\n\
         \n\
         2012-02-02 balance Assets:Bank  1000 USD\n",
    );

    // Issue the codeLens request and immediately fire the nvim
    // cancellation quirk. The codeLens path is synchronously
    // dispatched (see test rustdoc), so the cancel won't actually
    // race the response in-harness — but we still send it as
    // belt-and-braces in case a future refactor moves codeLens into
    // async dispatch.
    let id = client.next_request_id();
    let req = lsp_server::Request {
        id: id.clone(),
        method: <CodeLensRequest as lsp_types::request::Request>::METHOD.to_string(),
        params: serde_json::to_value(CodeLensParams {
            text_document: TextDocumentIdentifier {
                uri: uri.parse().unwrap(),
            },
            work_done_progress_params: Default::default(),
            partial_result_params: Default::default(),
        })
        .unwrap(),
    };
    client.raw_send_request(req).expect("send codeLens request");
    quirks::nvim_cancel_race(&client, &id);

    // Drain messages manually until the codeLens response arrives,
    // capturing every publishDiagnostics along the way. This avoids
    // the fixed-timeout drain pattern that has a timing window: on
    // slow CI, a didOpen diagnostic could be in-flight when a
    // pre-codeLens drain times out, then be silently consumed by
    // `expect_response_timeout` and missed by a post-response drain.
    // The manual loop captures everything between request and
    // response, which is exactly the window the server has to
    // publish diagnostics for the document we just opened.
    let mut diagnostic_payloads: Vec<lsp_types::PublishDiagnosticsParams> = Vec::new();
    let deadline = Instant::now() + Duration::from_secs(10);
    let resp = loop {
        let remaining = deadline.saturating_duration_since(Instant::now());
        let msg = client
            .recv_with_timeout(remaining)
            .expect("timed out waiting for codeLens response");
        match msg {
            lsp_server::Message::Response(r) if r.id == id => break r,
            lsp_server::Message::Notification(n)
                if n.method == "textDocument/publishDiagnostics" =>
            {
                let p: lsp_types::PublishDiagnosticsParams =
                    serde_json::from_value(n.params).unwrap();
                diagnostic_payloads.push(p);
            }
            // Other notifications and unrelated responses are
            // discarded (no test currently asserts on them).
            _ => {}
        }
    };

    let bad: Vec<_> = diagnostic_payloads
        .iter()
        .filter(|p| !p.diagnostics.is_empty())
        .collect();
    assert!(
        bad.is_empty(),
        "valid balance assertion must not produce any diagnostic; \
         the user reported #1253's lens looking like an error, but \
         the underlying validator must not flag it. captured payloads: \
         {bad:?}"
    );

    let result = resp
        .result
        .expect("server returned a result, not an error, for cancelled-but-completed codeLens");
    let lenses: Option<Vec<lsp_types::CodeLens>> = serde_json::from_value(result).unwrap();
    let lenses = lenses.expect("lenses should be Some on a non-empty document");

    let balance_lens = lenses
        .iter()
        .find(|l| {
            l.command
                .as_ref()
                .is_some_and(|c| c.title.contains("Balance:"))
        })
        .expect("balance lens emitted");

    let cmd = balance_lens
        .command
        .as_ref()
        .expect("balance lens carries a command (no placeholder, no resolve)");
    assert!(
        cmd.title.contains('✓'),
        "issue #1253: passing assertion must ship with the real ✓ \
         title on the initial response, not a `(checking…)` \
         placeholder. got {:?}",
        cmd.title
    );
    assert!(
        !cmd.title.contains("checking"),
        "issue #1253: title must not contain the `(checking…)` \
         placeholder; that's the stuck-state symptom. got {:?}",
        cmd.title
    );
    assert!(
        balance_lens.data.is_none(),
        "issue #1253: balance lens must not carry a resolve-data \
         payload; the round-trip is what nvim could race against. \
         got data = {:?}",
        balance_lens.data
    );
}

/// Exercise the async-dispatch path of `try_dispatch_async`.
///
/// `semanticTokens/full` is one of the two async-dispatched request
/// methods (the other is `codeLens/resolve`). The dispatch sends the
/// request to a background worker, then the worker's result is routed
/// back through `Event::Task` to the main loop and out as a response.
///
/// This test pins that the async round-trip works end to end: a
/// successful response with a `data` array reaches the client. The
/// codeLens smoke test alone would not catch a regression in the
/// async event loop (codeLens is synchronously dispatched).
#[test]
fn semantic_tokens_round_trip_through_async_dispatch() {
    let mut client = LspTestClient::spawn();
    client.initialize();

    let uri = test_uri("semtok.beancount");
    client.open_document(
        &uri,
        "2024-01-01 open Assets:Cash USD\n\
         2024-02-01 * \"Coffee\"\n  \
           Assets:Cash  -5.00 USD\n  \
           Expenses:Food\n",
    );

    let tokens: Option<lsp_types::SemanticTokensResult> = client
        .request::<SemanticTokensFullRequest>(SemanticTokensParams {
            text_document: TextDocumentIdentifier {
                uri: uri.parse().unwrap(),
            },
            work_done_progress_params: Default::default(),
            partial_result_params: Default::default(),
        });

    let tokens = tokens.expect("semanticTokens/full returns Some on a parsed document");
    let data_len = match tokens {
        lsp_types::SemanticTokensResult::Tokens(t) => t.data.len(),
        lsp_types::SemanticTokensResult::Partial(p) => p.data.len(),
    };
    assert!(
        data_len > 0,
        "non-empty document must produce at least one semantic token \
         delta entry"
    );
}

/// An unknown LSP method must come back as a structured JSON-RPC error
/// (MethodNotFound = -32601), not as a server panic, a dropped
/// connection, or a 200-OK-with-garbage. This is the behavior the
/// `DispatchError::MethodNotFound` arm encodes; if a future refactor
/// swaps the error code or stops emitting a response at all, this
/// test catches it before users do.
#[test]
fn unknown_method_returns_method_not_found_error() {
    let mut client = LspTestClient::spawn();
    client.initialize();

    let id = client.next_request_id();
    client
        .raw_send_request(lsp_server::Request {
            id: id.clone(),
            method: "textDocument/doesNotExist".to_string(),
            params: serde_json::json!({}),
        })
        .expect("send bogus request");

    let resp = client.expect_response(&id);
    let err = resp
        .error
        .expect("server returned an error, not a result, for an unknown method");
    assert_eq!(
        err.code,
        lsp_server::ErrorCode::MethodNotFound as i32,
        "unknown method must map to JSON-RPC -32601 MethodNotFound; \
         got code {} with message {:?}",
        err.code,
        err.message
    );
}

/// `codeLens/resolve` is dispatched through `try_dispatch_async` to the
/// background worker (`main_loop::try_dispatch_async` line 333), so a
/// real resolve request exercises:
///   1. `req.params` deserialization into `CodeLens`
///   2. `dispatch_async` id propagation through the task channel
///   3. `Event::Task` routing back to the main loop
///   4. response delivery
///
/// Today every lens kind ships with `command: Some(...)` after #1253,
/// so `handle_code_lens_resolve` only ever takes the
/// `command.is_none()` defensive branch on the wire. This test sends
/// a synthetic `command: None` lens and verifies the fallback
/// produces the documented `rledger.noop` command. If a future change
/// breaks the async dispatch wiring (wrong id propagation, lost
/// response, panic in the worker), the smoke would be lost without
/// a test that drives the full path.
#[test]
fn code_lens_resolve_round_trip_through_async_dispatch() {
    let mut client = LspTestClient::spawn();
    client.initialize();

    // No didOpen needed: the resolve fallback doesn't read document
    // state (signature dropped its parse_result + ledger_directives
    // params in PR #1261). We just send a synthetic lens with
    // command: None and assert on the round-trip.
    let synthetic_lens = lsp_types::CodeLens {
        range: lsp_types::Range {
            start: lsp_types::Position::new(0, 0),
            end: lsp_types::Position::new(0, 0),
        },
        command: None,
        data: None,
    };

    let resolved: lsp_types::CodeLens = client.request::<CodeLensResolve>(synthetic_lens);

    let cmd = resolved
        .command
        .expect("defensive fallback must populate command on a command:None lens");
    assert_eq!(
        cmd.command, "rledger.noop",
        "fallback command must be rledger.noop so strict clients \
         render something benign instead of nvim's literal \
         'Unresolved lens'. got {:?}",
        cmd.command
    );
}

/// Regression for issue #1264: a balance lens carrying
/// `⚠ ... (see diagnostic)` MUST correspond to a real ERROR diagnostic
/// at the same line. Pre-#1264 the lens ran its own evaluator that
/// dropped plugins (`effective_date`, `lazy_balance`, ...) and
/// silently disagreed with `rledger check` — producing the dead-link
/// UX of a ⚠ lens pointing at a diagnostic that didn't exist.
///
/// The structural fix is for the lens to consult the validator's
/// diagnostic cache instead of re-deriving. This test pins the
/// dead-link-impossibility invariant at the protocol level:
/// drain all publishDiagnostics, request codeLens, and verify every
/// ⚠ lens line is matched by an ERROR diagnostic line. The test
/// doesn't need the effective_date plugin to actually load — the
/// invariant holds regardless of what the validator computes, because
/// the lens now follows the validator.
///
/// The document used is the exact reproduction from the issue.
#[test]
fn issue_1264_no_balance_lens_without_matching_diagnostic() {
    let mut client = LspTestClient::spawn();
    client.initialize();

    let uri = test_uri("issue_1264.beancount");
    // Exact bytes from the issue: effective_date plugin shifts the
    // 2012-02-03 food purchase to 2012-02-05, so balance assertions
    // on 02-03 through 02-04 pass at 1000 USD (validator's verdict).
    let source = "option \"operating_currency\" \"USD\"\n\
\n\
2012-01-01 open Assets:Bank\n\
2012-01-01 open Equity:Transfer\n\
2012-01-01 open Expenses:Food\n\
2012-01-01 open Income:Employment\n\
\n\
plugin \"beancount_reds_plugins.effective_date.effective_date\" \"{\n\
  'Assets':   {'earlier': 'Equity:Transfer', 'later': 'Equity:Transfer'},\n\
}\"\n\
\n\
2012-02-01 * \"Salary\"\n  \
  Assets:Bank                   1000 USD\n  \
  Income:Employment\n\
\n\
2012-02-02 balance Assets:Bank  1000 USD\n\
\n\
2012-02-03 * \"Delayed food purchase\"\n  \
  Expenses:Food                  100 USD\n  \
  Assets:Bank                   -100 USD\n    \
    effective_date: 2012-02-05\n\
\n\
2012-02-03 balance Assets:Bank  1000 USD\n\
2012-02-04 balance Assets:Bank  1000 USD\n\
2012-02-05 balance Assets:Bank  1000 USD\n\
2012-02-06 balance Assets:Bank   900 USD\n";
    client.open_document(&uri, source);

    // Issue the codeLens request and drain everything until the
    // response arrives, capturing every publishDiagnostics on the way.
    // Same drain pattern as the #1253 test — guarantees we capture
    // the diagnostic state matching the codeLens response.
    let id = client.next_request_id();
    let req = lsp_server::Request {
        id: id.clone(),
        method: <CodeLensRequest as lsp_types::request::Request>::METHOD.to_string(),
        params: serde_json::to_value(CodeLensParams {
            text_document: TextDocumentIdentifier {
                uri: uri.parse().unwrap(),
            },
            work_done_progress_params: Default::default(),
            partial_result_params: Default::default(),
        })
        .unwrap(),
    };
    client.raw_send_request(req).expect("send codeLens request");

    let mut diagnostic_payloads: Vec<lsp_types::PublishDiagnosticsParams> = Vec::new();
    let deadline = Instant::now() + Duration::from_secs(15);
    let resp = loop {
        let remaining = deadline.saturating_duration_since(Instant::now());
        let msg = client
            .recv_with_timeout(remaining)
            .expect("timed out waiting for codeLens response");
        match msg {
            lsp_server::Message::Response(r) if r.id == id => break r,
            lsp_server::Message::Notification(n)
                if n.method == "textDocument/publishDiagnostics" =>
            {
                let p: lsp_types::PublishDiagnosticsParams =
                    serde_json::from_value(n.params).unwrap();
                diagnostic_payloads.push(p);
            }
            _ => {}
        }
    };

    let result = resp.result.expect("codeLens returned a result");
    let lenses: Option<Vec<lsp_types::CodeLens>> = serde_json::from_value(result).unwrap();
    let lenses = lenses.expect("lenses emitted on a non-empty document");

    // Latest diagnostics for our URI (the server may publish multiple
    // times; the last one is the authoritative current state). Fail
    // loudly if no publishDiagnostics arrived for the URI — otherwise
    // a URI-canonicalization mismatch (`p.uri.as_str()` vs the test's
    // `uri: String`) could silently fall through to an empty slice,
    // and a regression that emits ⚠ lenses without diagnostics could
    // still pass the assertion vacuously.
    let latest_payload = diagnostic_payloads
        .iter()
        .rev()
        .find(|p| p.uri.as_str() == uri)
        .unwrap_or_else(|| {
            panic!(
                "no publishDiagnostics arrived for {uri}; captured \
                 payloads: {:?}",
                diagnostic_payloads
                    .iter()
                    .map(|p| p.uri.as_str())
                    .collect::<Vec<_>>()
            )
        });
    let error_lines: std::collections::HashSet<u32> = latest_payload
        .diagnostics
        .iter()
        .filter(|d| d.severity == Some(lsp_types::DiagnosticSeverity::ERROR))
        .map(|d| d.range.start.line)
        .collect();

    // The dead-link-impossibility invariant: every ⚠ balance lens
    // (which says "see diagnostic") must have a real ERROR diagnostic
    // at the same line.
    let dead_links: Vec<_> = lenses
        .iter()
        .filter(|l| {
            let title = l.command.as_ref().map(|c| c.title.as_str()).unwrap_or("");
            title.contains("Balance:") && title.contains("see diagnostic")
        })
        .filter(|l| !error_lines.contains(&l.range.start.line))
        .collect();

    assert!(
        dead_links.is_empty(),
        "issue #1264: balance lens(es) carry `(see diagnostic)` but no \
         ERROR diagnostic exists at the same line(s). This is exactly \
         the dead-link UX the issue reported. error lines: {error_lines:?}, \
         dead-link lenses: {dead_links:?}"
    );
}

/// Companion to `issue_1264_no_balance_lens_without_matching_diagnostic`:
/// the opposite direction. A real balance-arithmetic failure (validator
/// emits `E2001`) MUST surface as `⚠ Balance: X USD (see diagnostic)`
/// on the lens, with a matching diagnostic at the same line.
///
/// Without this assertion, a future regression where the lens reads
/// the wrong cache key, URI canonicalization drifts, or the new
/// `validation_would_run` gate is misconfigured would silently
/// downgrade every failing assertion to ✓ — the inverse of #1264 and
/// just as misleading. The one-direction test (`issue_1264_*`) only
/// catches the false-⚠ class; this catches the false-✓ class.
#[test]
fn real_balance_failure_round_trips_to_warning_lens() {
    let mut client = LspTestClient::spawn();
    client.initialize();

    let uri = test_uri("real_balance_failure.beancount");
    // Deposit 50, assert 100 — guaranteed to fail balance-arithmetic.
    let source = "2024-01-01 open Assets:Bank USD\n\
2024-01-01 open Income:Salary\n\
2024-01-15 * \"Deposit\"\n  \
  Assets:Bank  50.00 USD\n  \
  Income:Salary\n\
2024-01-31 balance Assets:Bank 100 USD\n";
    client.open_document(&uri, source);

    let id = client.next_request_id();
    let req = lsp_server::Request {
        id: id.clone(),
        method: <CodeLensRequest as lsp_types::request::Request>::METHOD.to_string(),
        params: serde_json::to_value(CodeLensParams {
            text_document: TextDocumentIdentifier {
                uri: uri.parse().unwrap(),
            },
            work_done_progress_params: Default::default(),
            partial_result_params: Default::default(),
        })
        .unwrap(),
    };
    client.raw_send_request(req).expect("send codeLens request");

    let mut diagnostic_payloads: Vec<lsp_types::PublishDiagnosticsParams> = Vec::new();
    let deadline = Instant::now() + Duration::from_secs(15);
    let resp = loop {
        let remaining = deadline.saturating_duration_since(Instant::now());
        let msg = client
            .recv_with_timeout(remaining)
            .expect("timed out waiting for codeLens response");
        match msg {
            lsp_server::Message::Response(r) if r.id == id => break r,
            lsp_server::Message::Notification(n)
                if n.method == "textDocument/publishDiagnostics" =>
            {
                let p: lsp_types::PublishDiagnosticsParams =
                    serde_json::from_value(n.params).unwrap();
                diagnostic_payloads.push(p);
            }
            _ => {}
        }
    };

    let result = resp.result.expect("codeLens returned a result");
    let lenses: Option<Vec<lsp_types::CodeLens>> = serde_json::from_value(result).unwrap();
    let lenses = lenses.expect("lenses emitted on a non-empty document");

    // Verify the validator emitted an E2001 (balance assertion failed)
    // diagnostic — otherwise the test premise is broken.
    let latest_payload = diagnostic_payloads
        .iter()
        .rev()
        .find(|p| p.uri.as_str() == uri)
        .unwrap_or_else(|| {
            panic!(
                "no publishDiagnostics arrived for {uri}; captured \
                 payloads: {:?}",
                diagnostic_payloads
                    .iter()
                    .map(|p| p.uri.as_str())
                    .collect::<Vec<_>>()
            )
        });
    let balance_error = latest_payload.diagnostics.iter().find(|d| {
        d.severity == Some(lsp_types::DiagnosticSeverity::ERROR)
            && matches!(
                &d.code,
                Some(lsp_types::NumberOrString::String(s)) if s == "E2001",
            )
    });
    let balance_error = balance_error.unwrap_or_else(|| {
        panic!(
            "test premise: validator must emit an E2001 for `balance \
             Assets:Bank 100 USD` against a 50 USD deposit. captured \
             diagnostics: {:?}",
            latest_payload.diagnostics
        )
    });

    // The balance lens for that line must be ⚠.
    let balance_lens = lenses
        .iter()
        .find(|l| {
            l.range.start.line == balance_error.range.start.line
                && l.command
                    .as_ref()
                    .is_some_and(|c| c.title.contains("Balance:"))
        })
        .unwrap_or_else(|| {
            panic!(
                "no balance lens emitted at line {} (where the E2001 \
                 lives). lenses: {:?}",
                balance_error.range.start.line, lenses
            )
        });
    let cmd = balance_lens.command.as_ref().expect("ships resolved");
    assert!(
        cmd.title.contains('⚠') && cmd.title.contains("see diagnostic"),
        "real validator failure (E2001) MUST surface as ⚠ on the \
         balance lens. got {:?}",
        cmd.title
    );
}

/// Replacement for the unit-level
/// `test_code_lens_balance_uses_full_ledger_in_multi_file_mode` deleted
/// in #1265. That test fed the old lens a multi-file directives
/// snapshot directly and asserted the lens used cross-file aggregation
/// (issue #470 coverage). The new lens reads from the validator's
/// diagnostic cache; cross-file aggregation now lives in the validator,
/// not the lens.
///
/// This protocol test pins the end-to-end story: a journal that
/// includes two files, where file A asserts a balance that's only
/// correct when file B's offsetting transaction is considered, must
/// produce a `✓` lens on file A. Without multi-file aggregation, the
/// validator would emit `E2001` on file A and the lens would render
/// `⚠`. The test passing means the validator's cross-file overlay
/// AND the lens's verdict propagation both work.
///
/// Gated on `cfg(unix)`: the `file://{path}` URI assembly below assumes
/// the path starts with `/` (POSIX absolute), so on Windows it would
/// produce `file://C:\...` (only two slashes plus drive letter) and
/// fail Uri parsing — or worse, parse to a non-canonical URI that the
/// server rejects and falls into single-file mode, producing a
/// misleading `⚠` for "balance assertion failed" instead of a clean
/// platform skip. `main_loop.rs` cfg-splits its URI assembly between
/// Unix (`file://{}`) and Windows (`file:///{}`); a Windows-portable
/// variant of this test would mirror that. Today CI is Linux-only, so
/// the gate is a guardrail for the future.
#[cfg(unix)]
#[test]
fn multi_file_balance_lens_reflects_cross_file_aggregation() {
    let tmp = tempfile::tempdir().expect("tempdir");
    let journal_path = tmp.path().join("journal.beancount");
    let bank_path = tmp.path().join("bank.beancount");
    let credit_card_path = tmp.path().join("credit_card.beancount");

    // bank.beancount asserts 4950 USD — only correct if credit_card.beancount's
    // -50 USD transfer is visible.
    std::fs::write(
        &bank_path,
        "2024-01-01 open Assets:Bank:Checking USD\n\
         2024-01-01 open Income:Salary\n\
         2024-01-15 * \"Paycheck\"\n  \
           Assets:Bank:Checking   5000 USD\n  \
           Income:Salary\n\
         2024-01-21 balance Assets:Bank:Checking 4950 USD\n",
    )
    .expect("write bank.beancount");
    std::fs::write(
        &credit_card_path,
        "2024-01-01 open Liabilities:Credit-Card\n\
         2024-01-20 * \"Pay off credit card\"\n  \
           Assets:Bank:Checking  -50 USD\n  \
           Liabilities:Credit-Card\n",
    )
    .expect("write credit_card.beancount");
    std::fs::write(
        &journal_path,
        format!(
            "include \"{}\"\ninclude \"{}\"\n",
            bank_path.display(),
            credit_card_path.display()
        ),
    )
    .expect("write journal.beancount");

    let mut client = LspTestClient::spawn_with_journal(Some(journal_path));
    client.initialize();

    let bank_uri = format!("file://{}", bank_path.display());
    let source = std::fs::read_to_string(&bank_path).expect("read bank");
    client.open_document(&bank_uri, &source);

    let id = client.next_request_id();
    let req = lsp_server::Request {
        id: id.clone(),
        method: <CodeLensRequest as lsp_types::request::Request>::METHOD.to_string(),
        params: serde_json::to_value(CodeLensParams {
            text_document: TextDocumentIdentifier {
                uri: bank_uri.parse().unwrap(),
            },
            work_done_progress_params: Default::default(),
            partial_result_params: Default::default(),
        })
        .unwrap(),
    };
    client.raw_send_request(req).expect("send codeLens request");

    let mut diagnostic_payloads: Vec<lsp_types::PublishDiagnosticsParams> = Vec::new();
    let deadline = Instant::now() + Duration::from_secs(15);
    let resp = loop {
        let remaining = deadline.saturating_duration_since(Instant::now());
        let msg = client
            .recv_with_timeout(remaining)
            .expect("timed out waiting for codeLens response");
        match msg {
            lsp_server::Message::Response(r) if r.id == id => break r,
            lsp_server::Message::Notification(n)
                if n.method == "textDocument/publishDiagnostics" =>
            {
                let p: lsp_types::PublishDiagnosticsParams =
                    serde_json::from_value(n.params).unwrap();
                diagnostic_payloads.push(p);
            }
            _ => {}
        }
    };

    let result = resp.result.expect("codeLens returned a result");
    let lenses: Option<Vec<lsp_types::CodeLens>> = serde_json::from_value(result).unwrap();
    let lenses = lenses.expect("lenses emitted");

    // bank.beancount's diagnostics must contain no E2001 for the
    // balance: the validator saw both files via the journal and
    // accepted the assertion.
    let bank_diags = diagnostic_payloads
        .iter()
        .rev()
        .find(|p| p.uri.as_str() == bank_uri)
        .unwrap_or_else(|| {
            panic!(
                "no publishDiagnostics for {bank_uri}; captured: {:?}",
                diagnostic_payloads
                    .iter()
                    .map(|p| p.uri.as_str())
                    .collect::<Vec<_>>()
            )
        });
    let unexpected_balance_error = bank_diags.diagnostics.iter().find(|d| {
        d.severity == Some(lsp_types::DiagnosticSeverity::ERROR)
            && matches!(
                &d.code,
                Some(lsp_types::NumberOrString::String(s)) if s == "E2001",
            )
    });
    assert!(
        unexpected_balance_error.is_none(),
        "multi-file validator should have aggregated the -50 USD from \
         credit_card.beancount; got an unexpected E2001 on bank.beancount: {:?}",
        unexpected_balance_error,
    );

    let balance_lens = lenses
        .iter()
        .find(|l| {
            l.command
                .as_ref()
                .is_some_and(|c| c.title.contains("Balance:"))
        })
        .expect("balance lens emitted");
    let cmd = balance_lens.command.as_ref().expect("ships resolved");
    assert!(
        cmd.title.contains('✓') && cmd.title.contains("4950"),
        "multi-file aggregation makes the assertion hold; lens must \
         reflect the validator's ✓ verdict. got {:?}",
        cmd.title
    );
}

/// Regression for F1 from the round-3 deep review: when a journal is
/// loaded AND the user opens a `.beancount` file that is NOT part of
/// the journal, `handle_code_lens_request`'s `contains_file` gate
/// must fall back to single-file mode rather than feed the lens the
/// other ledger's bookkeeping.
///
/// Pre-fix the snapshot was used unconditionally, so a scratch file
/// asserting `balance Assets:Bank 1000 USD` would render ⚠ against
/// the journal's (unrelated) Assets:Bank balance, with no diagnostic
/// to explain the warning.
#[test]
fn scratch_file_not_in_journal_uses_single_file_mode() {
    // Write a journal whose Assets:Bank ends 2024 at 100 USD.
    let tmp = tempfile::tempdir().expect("tempdir");
    let journal_path = tmp.path().join("journal.beancount");
    std::fs::write(
        &journal_path,
        "2024-01-01 open Assets:Bank USD\n\
         2024-01-01 open Income:Salary\n\
         2024-01-15 * \"Paycheck\"\n  \
           Assets:Bank   100 USD\n  \
           Income:Salary\n",
    )
    .expect("write journal");

    let mut client = LspTestClient::spawn_with_journal(Some(journal_path));
    client.initialize();

    // Now open a SCRATCH file (different path, NOT in the journal)
    // that asserts a balance the journal would fail (1000 USD). The
    // scratch file's own postings sum to 1000 USD; in single-file
    // mode the lens shows ✓. Pre-fix the snapshot path would have
    // shown ⚠ because the journal's Assets:Bank ends at 100.
    let scratch_uri = test_uri("scratch_not_in_journal.beancount");
    client.open_document(
        &scratch_uri,
        "2024-01-01 open Assets:Bank USD\n\
         2024-01-01 open Income:Other\n\
         2024-02-01 * \"Scratch deposit\"\n  \
           Assets:Bank   1000 USD\n  \
           Income:Other\n\
         2024-02-02 balance Assets:Bank 1000 USD\n",
    );

    let lenses: Option<Vec<lsp_types::CodeLens>> =
        client.request::<CodeLensRequest>(CodeLensParams {
            text_document: TextDocumentIdentifier {
                uri: scratch_uri.parse().unwrap(),
            },
            work_done_progress_params: Default::default(),
            partial_result_params: Default::default(),
        });
    let lenses = lenses.expect("scratch file has directives, lenses emitted");

    let balance_lens = lenses
        .iter()
        .find(|l| {
            l.command
                .as_ref()
                .is_some_and(|c| c.title.contains("Balance:"))
        })
        .expect("balance lens emitted on the scratch file");
    let cmd = balance_lens
        .command
        .as_ref()
        .expect("balance lens carries a command");
    assert!(
        cmd.title.contains('✓'),
        "scratch file's balance is valid against ITS OWN postings; \
         the contains_file gate must keep the journal's snapshot \
         from leaking into the scratch lens. got {:?}",
        cmd.title
    );
}

/// Reproduction for #1408: `completionItem/resolve` must return a SINGLE
/// `CompletionItem` (not an array — a protocol violation), and when a
/// `journalFile` is configured its documentation must aggregate over the whole
/// loaded ledger, not the ephemeral buffer the completion was triggered in.
#[cfg(unix)]
#[test]
fn completion_resolve_returns_single_item_and_uses_journal() {
    let tmp = tempfile::tempdir().expect("tempdir");
    let journal_path = tmp.path().join("main.beancount");
    std::fs::write(
        &journal_path,
        "2024-01-01 open Assets:Bank:Checking USD\n\
         2024-01-01 open Income:Salary\n\
         2024-01-15 * \"Paycheck\"\n  \
           Assets:Bank:Checking   5000 USD\n  \
           Income:Salary\n\
         2024-02-20 * \"Rent\"\n  \
           Assets:Bank:Checking  -1500 USD\n  \
           Expenses:Rent\n",
    )
    .expect("write journal");

    let mut client = LspTestClient::spawn_with_journal(Some(journal_path.clone()));
    client.initialize();

    // An *ephemeral* buffer distinct from the journal (mirrors a client's
    // __test__.bean completion buffer).
    let buf_uri = format!("file://{}", tmp.path().join("__buf__.beancount").display());
    client.open_document(&buf_uri, "2024-03-01 * \"x\"\n  Assets:Bank:Checking\n");

    // Resolve an account completion item whose `data.uri` points at the
    // ephemeral buffer — resolve must still aggregate over the loaded journal.
    let item = serde_json::json!({
        "label": "Assets:Bank:Checking",
        "detail": "Account",
        "data": { "uri": buf_uri },
    });
    let id = client.next_request_id();
    let req = lsp_server::Request {
        id: id.clone(),
        method: <lsp_types::request::ResolveCompletionItem as lsp_types::request::Request>::METHOD
            .to_string(),
        params: item,
    };
    client.raw_send_request(req).expect("send resolve");
    let resp = client.expect_response(&id);
    let result = resp.result.expect("resolve returned a result");

    // Finding 1: the result must be a single object, not an array.
    assert!(
        result.is_object(),
        "completionItem/resolve must return a single CompletionItem object, got: {result}"
    );

    // Finding 2: documentation must reflect the loaded journal (2 txns, 3500 net).
    let resolved: lsp_types::CompletionItem =
        serde_json::from_value(result).expect("deserialize CompletionItem");
    // The ledger summary is also surfaced in `detail` (issue #1408), where
    // clients that don't render the documentation popup can still see it.
    let detail = resolved.detail.clone().expect("detail summary set");
    assert!(
        detail.contains("3500") && detail.contains("2 txns"),
        "detail should summarize the journal balance/count; got: {detail}"
    );
    let doc = match resolved.documentation {
        Some(lsp_types::Documentation::MarkupContent(m)) => m.value,
        other => panic!("expected markdown documentation, got {other:?}"),
    };
    assert!(
        doc.contains("2 transactions"),
        "resolve should aggregate over the journal (2 txns); got:\n{doc}"
    );
    assert!(
        doc.contains("3500"),
        "resolve should show the journal balance 5000-1500=3500; got:\n{doc}"
    );
}

/// Regression for #2: a validation error living in an `include`d file that the
/// user has NOT opened must still be surfaced — the server publishes
/// diagnostics for the included file's own URI. Pre-fix the error was filtered
/// out (only the open file's errors were kept) and the included file, having no
/// open buffer, never received a `publishDiagnostics`, so the problem was
/// completely invisible.
///
/// `cfg(unix)`: the `file://{path}` URI assembly assumes a POSIX absolute path
/// (see `multi_file_balance_lens_reflects_cross_file_aggregation`).
#[cfg(unix)]
#[test]
fn included_file_validation_errors_are_published() {
    let tmp = tempfile::tempdir().expect("tempdir");
    let journal_path = tmp.path().join("journal.beancount");
    let good_path = tmp.path().join("good.beancount");
    let bad_path = tmp.path().join("bad.beancount");

    // good.beancount opens the accounts so the only error in bad.beancount is
    // the unbalanced transaction (no unopened-account noise).
    std::fs::write(
        &good_path,
        "2024-01-01 open Assets:Cash USD\n2024-01-01 open Expenses:Food USD\n",
    )
    .expect("write good");
    // bad.beancount: an unbalanced transaction (-5 vs +3).
    std::fs::write(
        &bad_path,
        "2024-02-01 * \"unbalanced in include\"\n  \
           Assets:Cash   -5 USD\n  \
           Expenses:Food   3 USD\n",
    )
    .expect("write bad");
    std::fs::write(
        &journal_path,
        format!(
            "include \"{}\"\ninclude \"{}\"\n",
            good_path.display(),
            bad_path.display()
        ),
    )
    .expect("write journal");

    let mut client = LspTestClient::spawn_with_journal(Some(journal_path));
    client.initialize();

    // Open ONLY good.beancount; bad.beancount stays unopened.
    let good_uri = format!("file://{}", good_path.display());
    let good_src = std::fs::read_to_string(&good_path).expect("read good");
    client.open_document(&good_uri, &good_src);

    let bad_uri = format!("file://{}", bad_path.display());

    // Drain publishDiagnostics until bad.beancount's (non-empty) arrive.
    let deadline = Instant::now() + Duration::from_secs(15);
    let mut seen: Vec<String> = Vec::new();
    let bad_diags = loop {
        let remaining = deadline.saturating_duration_since(Instant::now());
        if remaining.is_zero() {
            break None;
        }
        let Some(msg) = client.recv_with_timeout(remaining) else {
            break None;
        };
        if let lsp_server::Message::Notification(n) = msg
            && n.method == "textDocument/publishDiagnostics"
        {
            let p: lsp_types::PublishDiagnosticsParams =
                serde_json::from_value(n.params).expect("valid publishDiagnostics");
            seen.push(p.uri.as_str().to_string());
            if p.uri.as_str() == bad_uri && !p.diagnostics.is_empty() {
                break Some(p);
            }
        }
    };

    let bad_diags = bad_diags.unwrap_or_else(|| {
        panic!("no non-empty publishDiagnostics for the unopened included file {bad_uri}; saw URIs: {seen:?}")
    });
    let has_unbalanced = bad_diags.diagnostics.iter().any(|d| {
        d.severity == Some(lsp_types::DiagnosticSeverity::ERROR)
            && matches!(&d.code, Some(lsp_types::NumberOrString::String(s)) if s == "E3001")
    });
    assert!(
        has_unbalanced,
        "expected an E3001 (unbalanced) diagnostic for the unopened included file {bad_uri}; got {:?}",
        bad_diags.diagnostics
    );
}

/// Companion to the above: once the error in the unopened included file is
/// fixed, its diagnostics must be explicitly CLEARED (an empty publish), not
/// left lingering in the client. Exercises `publish_cross_file_diagnostics`'s
/// stale-clearing path via a watched-file change that reloads the journal.
#[cfg(unix)]
#[test]
fn included_file_diagnostics_are_cleared_when_fixed() {
    use lsp_types::{DidChangeWatchedFilesParams, FileChangeType, FileEvent};

    let tmp = tempfile::tempdir().expect("tempdir");
    let journal_path = tmp.path().join("journal.beancount");
    let good_path = tmp.path().join("good.beancount");
    let bad_path = tmp.path().join("bad.beancount");
    std::fs::write(
        &good_path,
        "2024-01-01 open Assets:Cash USD\n2024-01-01 open Expenses:Food USD\n",
    )
    .expect("write good");
    // Start unbalanced (-5 vs +3).
    std::fs::write(
        &bad_path,
        "2024-02-01 * \"x\"\n  Assets:Cash   -5 USD\n  Expenses:Food   3 USD\n",
    )
    .expect("write bad");
    std::fs::write(
        &journal_path,
        format!(
            "include \"{}\"\ninclude \"{}\"\n",
            good_path.display(),
            bad_path.display()
        ),
    )
    .expect("write journal");

    let mut client = LspTestClient::spawn_with_journal(Some(journal_path));
    client.initialize();
    let good_uri = format!("file://{}", good_path.display());
    client.open_document(
        &good_uri,
        &std::fs::read_to_string(&good_path).expect("read good"),
    );
    let bad_uri = format!("file://{}", bad_path.display());

    // Drain publishDiagnostics until bad.beancount reaches the desired emptiness.
    let drain = |client: &mut LspTestClient, want_empty: bool| -> bool {
        let deadline = Instant::now() + Duration::from_secs(15);
        loop {
            let remaining = deadline.saturating_duration_since(Instant::now());
            if remaining.is_zero() {
                return false;
            }
            let Some(msg) = client.recv_with_timeout(remaining) else {
                return false;
            };
            if let lsp_server::Message::Notification(n) = msg
                && n.method == "textDocument/publishDiagnostics"
            {
                let p: lsp_types::PublishDiagnosticsParams =
                    serde_json::from_value(n.params).expect("valid publishDiagnostics");
                if p.uri.as_str() == bad_uri && p.diagnostics.is_empty() == want_empty {
                    return true;
                }
            }
        }
    };

    assert!(
        drain(&mut client, false),
        "expected a non-empty diagnostic for the unopened included file first"
    );

    // Fix bad.beancount on disk and notify a watched-file change → the server
    // reloads the journal and revalidates the open document, which recomputes
    // (now-clean) cross-file diagnostics for bad.beancount.
    std::fs::write(
        &bad_path,
        "2024-02-01 * \"x\"\n  Assets:Cash   -5 USD\n  Expenses:Food   5 USD\n",
    )
    .expect("rewrite bad balanced");
    client.notify::<lsp_types::notification::DidChangeWatchedFiles>(DidChangeWatchedFilesParams {
        changes: vec![FileEvent {
            uri: bad_uri.parse().unwrap(),
            typ: FileChangeType::CHANGED,
        }],
    });

    assert!(
        drain(&mut client, true),
        "expected bad.beancount diagnostics to be cleared (empty publish) after the fix"
    );
}

/// An async-dispatched request (`semanticTokens/full`) invalidated by a
/// concurrent edit must still receive a response — previously the stale result
/// was silently dropped, leaving a strict client waiting forever. The response
/// is either the (raced-in) tokens or a `ContentModified` (-32801) error.
#[test]
fn async_request_invalidated_by_edit_still_gets_a_response() {
    let mut client = LspTestClient::spawn();
    client.initialize();

    let uri = test_uri("async_stale.beancount");
    // A large document so `semanticTokens/full` takes long enough to be
    // invalidated by the edit we send immediately after.
    let mut big = String::new();
    for i in 0..4000 {
        big.push_str(&format!("2024-01-01 open Assets:A{i} USD\n"));
    }
    client.open_document(&uri, &big);

    let id = client.next_request_id();
    let req = lsp_server::Request {
        id: id.clone(),
        method: <SemanticTokensFullRequest as lsp_types::request::Request>::METHOD.to_string(),
        params: serde_json::to_value(SemanticTokensParams {
            text_document: TextDocumentIdentifier {
                uri: uri.parse().unwrap(),
            },
            work_done_progress_params: Default::default(),
            partial_result_params: Default::default(),
        })
        .unwrap(),
    };
    client
        .raw_send_request(req)
        .expect("send semanticTokens/full");

    // Immediately invalidate the world with an edit (bumps the revision).
    client.notify::<lsp_types::notification::DidChangeTextDocument>(
        lsp_types::DidChangeTextDocumentParams {
            text_document: lsp_types::VersionedTextDocumentIdentifier {
                uri: uri.parse().unwrap(),
                version: 2,
            },
            content_changes: vec![lsp_types::TextDocumentContentChangeEvent {
                range: None,
                range_length: None,
                text: "2024-01-01 open Assets:Edited USD\n".to_string(),
            }],
        },
    );

    // The request MUST get a response (pre-fix it was dropped → client hang).
    let deadline = Instant::now() + Duration::from_secs(15);
    let resp = loop {
        let remaining = deadline.saturating_duration_since(Instant::now());
        assert!(
            !remaining.is_zero(),
            "timed out waiting for a response to the async request — it was likely dropped (the bug)"
        );
        let msg = client
            .recv_with_timeout(remaining)
            .expect("no response for the async request — it was dropped (the bug)");
        if let lsp_server::Message::Response(r) = msg
            && r.id == id
        {
            break r;
        }
    };
    // If the result raced in as stale, it must be reported as ContentModified.
    if let Some(err) = resp.error {
        assert_eq!(
            err.code, -32801,
            "a stale async result must be reported as ContentModified, got {err:?}"
        );
    }
}

/// Regression: `workspace/symbol` must search the whole loaded ledger, not just
/// open buffers — an account declared in an unopened `include`d file must be
/// findable. Pre-fix the search only consulted open documents.
#[cfg(unix)]
#[test]
fn workspace_symbol_finds_symbols_in_unopened_included_files() {
    use lsp_types::request::WorkspaceSymbolRequest;

    let tmp = tempfile::tempdir().expect("tempdir");
    let journal_path = tmp.path().join("journal.beancount");
    let main_path = tmp.path().join("main.beancount");
    let inc_path = tmp.path().join("inc.beancount");
    std::fs::write(&main_path, "2024-01-01 open Assets:Bank USD\n").expect("write main");
    std::fs::write(&inc_path, "2024-01-01 open Expenses:CrossFileOnly USD\n").expect("write inc");
    std::fs::write(
        &journal_path,
        format!(
            "include \"{}\"\ninclude \"{}\"\n",
            main_path.display(),
            inc_path.display()
        ),
    )
    .expect("write journal");

    let mut client = LspTestClient::spawn_with_journal(Some(journal_path));
    client.initialize();
    // Open only main.beancount; inc.beancount stays unopened.
    let main_uri = format!("file://{}", main_path.display());
    client.open_document(
        &main_uri,
        &std::fs::read_to_string(&main_path).expect("read main"),
    );

    let resp: Option<lsp_types::WorkspaceSymbolResponse> = client
        .request::<WorkspaceSymbolRequest>(lsp_types::WorkspaceSymbolParams {
            query: "CrossFileOnly".to_string(),
            work_done_progress_params: Default::default(),
            partial_result_params: Default::default(),
        });
    let symbols = match resp {
        Some(lsp_types::WorkspaceSymbolResponse::Flat(v)) => v,
        other => panic!("expected a flat workspace-symbol response, got {other:?}"),
    };
    assert!(
        symbols.iter().any(|s| s.name == "Expenses:CrossFileOnly"),
        "workspace/symbol must find an account from an unopened included file; got: {:?}",
        symbols.iter().map(|s| &s.name).collect::<Vec<_>>()
    );
}

/// Regression: renaming an account used across `include`d files must produce
/// edits for ALL files, not just the open one — otherwise the rename leaves
/// dangling references in the other files and corrupts the ledger.
#[cfg(unix)]
#[test]
#[allow(clippy::mutable_key_type)] // Uri keys in the WorkspaceEdit changes map are safe to read
fn rename_account_spans_included_files() {
    use lsp_types::request::Rename;

    let tmp = tempfile::tempdir().expect("tempdir");
    let journal_path = tmp.path().join("journal.beancount");
    let main_path = tmp.path().join("main.beancount");
    let inc_path = tmp.path().join("inc.beancount");
    // main opens Assets:Bank; inc uses it in a posting.
    std::fs::write(&main_path, "2024-01-01 open Assets:Bank USD\n").expect("write main");
    std::fs::write(
        &inc_path,
        "2024-01-01 open Expenses:Food USD\n\
         2024-02-01 * \"x\"\n  Assets:Bank  -5 USD\n  Expenses:Food  5 USD\n",
    )
    .expect("write inc");
    std::fs::write(
        &journal_path,
        format!(
            "include \"{}\"\ninclude \"{}\"\n",
            main_path.display(),
            inc_path.display()
        ),
    )
    .expect("write journal");

    let mut client = LspTestClient::spawn_with_journal(Some(journal_path));
    client.initialize();
    let main_uri = format!("file://{}", main_path.display());
    client.open_document(
        &main_uri,
        &std::fs::read_to_string(&main_path).expect("read main"),
    );

    // Rename `Assets:Bank` (col 16 on line 0 of main) -> `Assets:Checking`.
    let edit: Option<lsp_types::WorkspaceEdit> =
        client.request::<Rename>(lsp_types::RenameParams {
            text_document_position: lsp_types::TextDocumentPositionParams {
                text_document: TextDocumentIdentifier {
                    uri: main_uri.parse().unwrap(),
                },
                position: lsp_types::Position::new(0, 16),
            },
            new_name: "Assets:Checking".to_string(),
            work_done_progress_params: Default::default(),
        });

    let changes = edit
        .expect("rename returned an edit")
        .changes
        .expect("workspace edit has per-file changes");
    let inc_uri = format!("file://{}", inc_path.display());
    let edited_uris: Vec<&str> = changes.keys().map(|u| u.as_str()).collect();
    assert!(
        changes.keys().any(|u| u.as_str() == main_uri),
        "rename must edit the open file; edited: {edited_uris:?}"
    );
    assert!(
        changes.keys().any(|u| u.as_str() == inc_uri),
        "rename must also edit the included file (cross-file usage); edited: {edited_uris:?}"
    );
}
