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

use std::time::Duration;

use harness::{LspTestClient, test_uri};
use lsp_types::request::{CodeLensRequest, SemanticTokensFullRequest};
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

    // `on_did_open` calls `publish_diagnostics` synchronously, so any
    // diagnostic for the file is already in the channel by now. Drain
    // it BEFORE sending the codeLens request: `expect_response_timeout`
    // would silently consume it, and we want to assert on it later.
    // For a passing balance there should be zero non-empty
    // publishDiagnostics; capture any to surface in the assert below.
    let mut saw_diagnostic = false;
    while let Some(msg) = client.recv_with_timeout(Duration::from_millis(200)) {
        if let lsp_server::Message::Notification(n) = msg
            && n.method == "textDocument/publishDiagnostics"
        {
            let params: lsp_types::PublishDiagnosticsParams =
                serde_json::from_value(n.params).unwrap();
            if !params.diagnostics.is_empty() {
                saw_diagnostic = true;
                eprintln!("unexpected didOpen diagnostic: {:?}", params.diagnostics);
            }
        }
    }
    assert!(
        !saw_diagnostic,
        "valid balance assertion must not produce a diagnostic at \
         didOpen time; the user reported #1253's lens looking like an \
         error, but the underlying validator must not flag it"
    );

    // Issue the codeLens request. We capture its id so we can fire
    // a cancel "race" (see test rustdoc — this is structurally a
    // no-op given sync dispatch, but kept as belt-and-braces).
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

    // Wait for the response. Use a slightly-longer timeout because
    // this test starts a fresh server (cold cache) and books the
    // ledger.
    let resp = client.expect_response_timeout(&id, Duration::from_secs(10));

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
