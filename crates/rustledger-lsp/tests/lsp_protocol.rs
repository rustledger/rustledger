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
