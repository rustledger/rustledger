//! In-process LSP integration test harness.
//!
//! Spawns [`run_main_loop`] on a worker thread driven by an
//! `lsp_server::Connection::memory()` channel pair. Tests own the
//! client side of the pair and drive the server through real LSP
//! JSON-RPC messages.
//!
//! # Why this exists
//!
//! Pre-#1260 every LSP bug we caught in CI was at the *handler*
//! layer (functions in isolation). Bugs in the *protocol interaction*
//! layer (message sequencing, cancellation, state ordering) shipped
//! to users and were only reported via issues like #1245, #1253. The
//! handler-level tests passed because the handler returned the right
//! value when called directly; the failures lived in HOW the server
//! and client exchanged messages.
//!
//! This harness is the missing layer-2 testing infrastructure (see
//! the architecture discussion in `docs/development/lsp-support.md`). Tests
//! written against [`LspTestClient`] can:
//!
//! - issue real `textDocument/codeLens`, `textDocument/completion`,
//!   etc. requests and assert on the responses
//! - send `$/cancelRequest` notifications interleaved with requests
//!   to exercise cancellation races
//! - simulate specific client quirks via the [`quirks`] module
//!
//! # Layering
//!
//! - **Unit tests** (in `src/handlers/*.rs`): handler-as-function
//!   tests. Cheap, fast, no protocol layer.
//! - **Integration tests** (this harness): protocol round-trip
//!   tests. Cover sequencing, cancellation, multi-message flows.
//! - **Manual smoke** (`docs/development/lsp-support.md`): verify in real nvim
//!   and VS Code before merging anything that changes lens or
//!   diagnostic display.
//!
//! See `docs/development/lsp-support.md` for the full testing taxonomy and the
//! supported-client contract.

use std::path::PathBuf;
use std::time::{Duration, Instant};

use lsp_server::{Connection, Message, Notification, Request, RequestId, Response};
use lsp_types::notification::Notification as NotificationTrait;
use lsp_types::request::Request as RequestTrait;
use serde::Serialize;
use serde::de::DeserializeOwned;

use rustledger_lsp::handlers::utils::PositionEncoding;
use rustledger_lsp::main_loop::run_main_loop;

/// Default timeout for any blocking receive in the harness.
///
/// Generous enough to absorb cold-cache cargo-test runs on slower
/// CI workers (booking + plugins can take 100ms+ on first call) and
/// short enough that a stuck test fails the suite rather than hanging
/// it. A test that legitimately needs longer should pass an explicit
/// duration to [`LspTestClient::expect_response_timeout`].
pub const DEFAULT_TIMEOUT: Duration = Duration::from_secs(5);

/// An in-process LSP client connected to a freshly-spawned server.
///
/// On construction, spawns a worker thread that runs the server's
/// initialize handshake + [`run_main_loop`]. The client side of the
/// memory connection is owned by this struct.
///
/// Drop the client to shut down the server cleanly: the channel
/// drop triggers `run_main_loop`'s loop to exit, the worker thread
/// joins.
pub struct LspTestClient {
    /// Held in an `Option` so `Drop` can `take()` and explicitly drop
    /// the connection BEFORE joining the server thread. Dropping the
    /// sender closes the server's receive channel, which is how
    /// `run_main_loop` is signaled to exit. (We avoid the real `exit`
    /// notification because `handle_notification` calls
    /// `std::process::exit`, which would terminate the test binary
    /// mid-suite.)
    client: Option<Connection>,
    next_request_id: i32,
    /// Server thread join handle. Kept so `Drop` can wait briefly
    /// for clean shutdown; held in an `Option` so we can `take()` it.
    server_thread: Option<std::thread::JoinHandle<()>>,
}

impl LspTestClient {
    /// Spawn a server and return a connected client. The
    /// initialize/initialized handshake has not been performed yet;
    /// call [`Self::initialize`] before sending other requests.
    #[must_use]
    pub fn spawn() -> Self {
        Self::spawn_with_journal(None)
    }

    /// Spawn a server backed by `journal_file` for multi-file mode.
    /// `None` is single-file mode (the LSP path most users follow).
    #[must_use]
    pub fn spawn_with_journal(journal_file: Option<PathBuf>) -> Self {
        let (server, client) = Connection::memory();

        let server_thread = std::thread::spawn(move || {
            // Mirror `server::start_stdio`'s initialize handshake on
            // the server side. The test client sends `initialize`
            // as its first message; we accept it and reply with a
            // minimal `InitializeResult`. Position encoding is
            // hard-coded UTF-8 here (what modern clients negotiate);
            // tests that need UTF-16 behavior can switch via a
            // separate constructor (not yet needed).
            let (id, _params) = match server.initialize_start() {
                Ok(pair) => pair,
                Err(e) => {
                    eprintln!("[harness server] initialize_start failed: {e}");
                    return;
                }
            };

            let init_result = serde_json::json!({
                "capabilities": minimal_server_capabilities(),
                "serverInfo": { "name": "rustledger-lsp-test", "version": "0.0.0" },
            });

            if let Err(e) = server.initialize_finish(id, init_result) {
                eprintln!("[harness server] initialize_finish failed: {e}");
                return;
            }

            run_main_loop(server.receiver, server.sender, None, PositionEncoding::Utf8);
            let _ = journal_file; // reserved for a future multi-file harness
        });

        Self {
            client: Some(client),
            next_request_id: 1,
            server_thread: Some(server_thread),
        }
    }

    /// Access the underlying `Connection`. Always returns `Some`
    /// during the lifetime of normal test code; the inner `Option`
    /// only becomes `None` inside [`Drop::drop`].
    fn conn(&self) -> &Connection {
        self.client
            .as_ref()
            .expect("connection accessed after harness drop")
    }

    /// Perform the `initialize` + `initialized` handshake.
    pub fn initialize(&mut self) {
        let init_params = lsp_types::InitializeParams {
            capabilities: lsp_types::ClientCapabilities {
                general: Some(lsp_types::GeneralClientCapabilities {
                    position_encodings: Some(vec![lsp_types::PositionEncodingKind::UTF8]),
                    ..Default::default()
                }),
                ..Default::default()
            },
            ..Default::default()
        };

        let _ = self.request::<lsp_types::request::Initialize>(init_params);
        self.notify::<lsp_types::notification::Initialized>(lsp_types::InitializedParams {});
    }

    /// Send a `textDocument/didOpen` notification for `uri` with
    /// `text` as the document body.
    pub fn open_document(&self, uri: &str, text: &str) {
        let params = lsp_types::DidOpenTextDocumentParams {
            text_document: lsp_types::TextDocumentItem {
                uri: uri.parse().expect("test uri must parse"),
                language_id: "beancount".to_string(),
                version: 1,
                text: text.to_string(),
            },
        };
        self.notify::<lsp_types::notification::DidOpenTextDocument>(params);
    }

    /// Send a typed LSP request and block until the matching response
    /// arrives. Returns the deserialized response payload.
    ///
    /// # Panics
    ///
    /// Panics if the server returns an error response or the
    /// payload fails to deserialize. Tests that expect an error
    /// response should use [`Self::request_raw`].
    pub fn request<R>(&mut self, params: R::Params) -> R::Result
    where
        R: RequestTrait,
        R::Params: Serialize,
        R::Result: DeserializeOwned,
    {
        let id = self.next_request_id();
        let req = Request {
            id: id.clone(),
            method: R::METHOD.to_string(),
            params: serde_json::to_value(params).expect("params serialize"),
        };
        self.conn()
            .sender
            .send(Message::Request(req))
            .expect("send to server");

        let resp = self.expect_response(&id);
        let result = resp
            .result
            .unwrap_or_else(|| panic!("server returned error on {}: {:?}", R::METHOD, resp.error));
        serde_json::from_value(result).expect("response deserialize")
    }

    /// Send a pre-built `lsp_server::Request` without waiting for the
    /// response. Returns immediately after the message is on the wire.
    ///
    /// Tests use this when they need to interleave a follow-up message
    /// (typically `$/cancelRequest`) between issuing a request and
    /// receiving its response. The typed [`Self::request`] blocks
    /// until the response arrives, which is the wrong primitive for
    /// race tests.
    ///
    /// Pair with [`Self::expect_response`] / [`Self::expect_response_timeout`]
    /// to retrieve the response later.
    pub fn raw_send_request(
        &self,
        req: Request,
    ) -> Result<(), crossbeam_channel::SendError<Message>> {
        self.conn().sender.send(Message::Request(req))
    }

    /// Send a typed notification.
    pub fn notify<N>(&self, params: N::Params)
    where
        N: NotificationTrait,
        N::Params: Serialize,
    {
        let notif = Notification {
            method: N::METHOD.to_string(),
            params: serde_json::to_value(params).expect("params serialize"),
        };
        self.conn()
            .sender
            .send(Message::Notification(notif))
            .expect("send to server");
    }

    /// Block until the response matching `id` arrives, draining any
    /// server-initiated messages (notifications, requests) in the
    /// meantime. Server notifications are silently dropped; tests
    /// that want to observe them should use
    /// [`Self::recv_with_timeout`] explicitly before issuing the
    /// request whose response they care about.
    ///
    /// # Panics
    ///
    /// Panics on timeout or if the server channel closes.
    pub fn expect_response(&self, id: &RequestId) -> Response {
        self.expect_response_timeout(id, DEFAULT_TIMEOUT)
    }

    /// Same as [`Self::expect_response`] but with a caller-supplied
    /// timeout. Useful for tests that need to wait longer than the
    /// default (cold-cache cargo-test, heavy fixtures).
    pub fn expect_response_timeout(&self, id: &RequestId, timeout: Duration) -> Response {
        let deadline = Instant::now() + timeout;
        loop {
            let remaining = deadline.saturating_duration_since(Instant::now());
            let msg = self
                .conn()
                .receiver
                .recv_timeout(remaining)
                .unwrap_or_else(|e| panic!("timed out waiting for response to {id:?}: {e}"));
            match msg {
                Message::Response(resp) if resp.id == *id => return resp,
                Message::Response(_) | Message::Notification(_) | Message::Request(_) => {
                    // Drain server-initiated traffic the test isn't
                    // interested in. A future test that needs to
                    // observe specific server messages can use
                    // `recv_with_timeout` before calling
                    // `expect_response`.
                }
            }
        }
    }

    /// Receive whatever the server sends next (response, notification,
    /// or request). Useful for tests that want to inspect the
    /// server's publishDiagnostics or showMessage traffic.
    pub fn recv_with_timeout(&self, timeout: Duration) -> Option<Message> {
        self.conn().receiver.recv_timeout(timeout).ok()
    }

    /// Send a `$/cancelRequest` for `id`. The server may still
    /// respond to the request (the cancellation race we're explicitly
    /// testing for some tests); other tests use this to verify the
    /// server *honors* cancellation. See [`quirks::nvim_cancel_race`]
    /// for the typical use site.
    pub fn cancel(&self, id: &RequestId) {
        let params = serde_json::json!({ "id": id });
        let notif = Notification {
            method: "$/cancelRequest".to_string(),
            params,
        };
        self.conn()
            .sender
            .send(Message::Notification(notif))
            .expect("send cancel");
    }

    /// Allocate the next request id and return it as an
    /// `lsp_server::RequestId`.
    pub fn next_request_id(&mut self) -> RequestId {
        let id = RequestId::from(self.next_request_id);
        self.next_request_id += 1;
        id
    }

    /// Send the `shutdown` request as a best-effort protocol-clean
    /// cleanup. Deliberately does NOT send the `exit` notification:
    /// `main_loop`'s `exit` handler calls [`std::process::exit`],
    /// which would terminate the cargo-test process mid-suite (and
    /// take every other test in this binary with it).
    ///
    /// The server is actually wound down by dropping the connection
    /// in [`Drop::drop`]: channel closure makes `run_main_loop`'s
    /// `select!` return `Err`, which breaks the loop normally.
    fn shutdown(&mut self) {
        let id = self.next_request_id();
        let _ = self.conn().sender.send(Message::Request(Request {
            id,
            method: "shutdown".to_string(),
            params: serde_json::json!(null),
        }));
    }
}

impl Drop for LspTestClient {
    fn drop(&mut self) {
        self.shutdown();
        // Drop the connection BEFORE join: closing the sender is what
        // makes the server's `select! recv(receiver)` return `Err`
        // and `run_main_loop` break out cleanly. Without this, the
        // server thread would block forever and the join would hang.
        drop(self.client.take());
        if let Some(handle) = self.server_thread.take() {
            let _ = handle.join();
        }
    }
}

/// Minimal `ServerCapabilities` value used by the harness. Tests
/// shouldn't need to inspect what's advertised; the real server's
/// capabilities are exercised by handler-specific tests in
/// `src/handlers/`. The harness just needs SOME capabilities object
/// to satisfy `initialize_finish`.
fn minimal_server_capabilities() -> serde_json::Value {
    serde_json::json!({
        "positionEncoding": "utf-8",
        "textDocumentSync": 1,
        "codeLensProvider": { "resolveProvider": true },
        "completionProvider": { "resolveProvider": true },
        "diagnosticProvider": null,
    })
}

/// Compose a typical `file://` URI for a test document. Use this so
/// every test agrees on the URI format without each one having to
/// remember the `file:///` prefix.
#[must_use]
pub fn test_uri(name: &str) -> String {
    format!("file:///{}", name)
}
