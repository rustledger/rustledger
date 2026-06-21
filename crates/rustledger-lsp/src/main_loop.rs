//! Main event loop for the LSP server.
//!
//! Follows rust-analyzer's architecture:
//! - Notifications handled synchronously (critical for correctness)
//! - Requests dispatched to threadpool with immutable snapshots
//! - Revision counter enables cancellation of stale requests

use crate::handlers::call_hierarchy::{
    handle_incoming_calls, handle_outgoing_calls, handle_prepare_call_hierarchy,
};
use crate::handlers::code_actions::{handle_code_action_resolve, handle_code_actions};
use crate::handlers::code_lens::{handle_code_lens, handle_code_lens_resolve};
use crate::handlers::completion::handle_completion;
use crate::handlers::completion_resolve::handle_completion_resolve;
use crate::handlers::declaration::handle_goto_declaration;
use crate::handlers::definition::handle_goto_definition;
use crate::handlers::diagnostics::all_diagnostics;
use crate::handlers::document_color::{handle_color_presentation, handle_document_color};
use crate::handlers::document_highlight::handle_document_highlight;
use crate::handlers::document_links::{handle_document_link_resolve, handle_document_links};
use crate::handlers::execute_command::handle_execute_command;
use crate::handlers::folding::handle_folding_ranges;
use crate::handlers::formatting::handle_formatting;
use crate::handlers::hover::handle_hover;
use crate::handlers::inlay_hints::{handle_inlay_hint_resolve, handle_inlay_hints};
use crate::handlers::linked_editing::handle_linked_editing_range;
use crate::handlers::on_type_formatting::handle_on_type_formatting;
use crate::handlers::range_formatting::handle_range_formatting;
use crate::handlers::references::handle_references;
use crate::handlers::rename::{handle_prepare_rename, handle_rename};
use crate::handlers::selection_range::handle_selection_range;
use crate::handlers::semantic_tokens::{
    handle_semantic_tokens, handle_semantic_tokens_delta, handle_semantic_tokens_range,
};
use crate::handlers::signature_help::handle_signature_help;
use crate::handlers::symbols::handle_document_symbols;
use crate::handlers::type_hierarchy::{
    handle_prepare_type_hierarchy, handle_subtypes, handle_supertypes,
};
use crate::handlers::workspace_symbols::handle_workspace_symbols;
use crate::ledger_state::{SharedLedgerState, new_shared_ledger_state};
use crate::uri_to_path;
use crate::vfs::Vfs;
use crossbeam_channel::{Receiver, Sender};
use lsp_types::notification::{
    DidChangeTextDocument, DidChangeWatchedFiles, DidCloseTextDocument, DidOpenTextDocument,
    Notification, PublishDiagnostics,
};
use lsp_types::request::{
    CallHierarchyIncomingCalls, CallHierarchyOutgoingCalls, CallHierarchyPrepare,
    CodeActionRequest, CodeActionResolveRequest, CodeLensRequest, CodeLensResolve,
    ColorPresentationRequest, Completion, DocumentColor, DocumentHighlightRequest,
    DocumentLinkRequest, DocumentLinkResolve, DocumentSymbolRequest, ExecuteCommand,
    FoldingRangeRequest, Formatting, GotoDeclaration, GotoDefinition, HoverRequest, Initialize,
    InlayHintRequest, InlayHintResolveRequest, LinkedEditingRange, OnTypeFormatting,
    PrepareRenameRequest, RangeFormatting, References, Rename, Request, ResolveCompletionItem,
    SelectionRangeRequest, SemanticTokensFullDeltaRequest, SemanticTokensFullRequest,
    SemanticTokensRangeRequest, Shutdown, SignatureHelpRequest, TypeHierarchyPrepare,
    TypeHierarchySubtypes, TypeHierarchySupertypes, WorkspaceSymbolRequest,
};
use lsp_types::{
    CallHierarchyIncomingCallsParams, CallHierarchyOutgoingCallsParams, CallHierarchyPrepareParams,
    CodeAction, CodeActionParams, CodeLens, CodeLensParams, ColorPresentationParams,
    CompletionItem, CompletionParams, DocumentColorParams, DocumentFormattingParams,
    DocumentHighlightParams, DocumentLink, DocumentLinkParams, DocumentOnTypeFormattingParams,
    DocumentRangeFormattingParams, DocumentSymbolParams, ExecuteCommandParams, FoldingRangeParams,
    GotoDefinitionParams, HoverParams, InitializeParams, InlayHint, InlayHintParams,
    LinkedEditingRangeParams, PublishDiagnosticsParams, ReferenceParams, RenameParams,
    SelectionRangeParams, SemanticTokensDeltaParams, SemanticTokensParams,
    SemanticTokensRangeParams, SignatureHelpParams, TextDocumentPositionParams,
    TypeHierarchyPrepareParams, TypeHierarchySubtypesParams, TypeHierarchySupertypesParams, Uri,
    WorkspaceSymbolParams,
};
use parking_lot::RwLock;
use rustledger_core::Directive;
use rustledger_parser::{ParseResult, Spanned, parse};
use std::collections::HashMap;
use std::path::PathBuf;
use std::sync::Arc;

/// Events processed by the main loop.
#[derive(Debug)]
pub enum Event {
    /// LSP message from the client.
    Message(Message),
    /// Response from a background task (dispatched via threadpool).
    Task(TaskResult),
}

/// LSP message types.
#[derive(Debug)]
pub enum Message {
    /// Request from client (expects response).
    Request(lsp_server::Request),
    /// Notification from client (no response).
    Notification(lsp_server::Notification),
    /// Response from client (for server-initiated requests).
    Response(lsp_server::Response),
}

/// Result from a background task.
#[derive(Debug)]
pub struct TaskResult {
    /// The request ID this task is responding to.
    pub request_id: lsp_server::RequestId,
    /// The result of the task, or an error message.
    pub result: Result<serde_json::Value, String>,
}

/// A job to be executed on the background worker thread.
type BackgroundJob = Box<dyn FnOnce() + Send>;

/// Structured failure reasons emitted by the request-dispatch loop.
///
/// Each variant maps deterministically to an LSP `ErrorCode` via
/// [`DispatchError::error_code`]. Round-20 introduced this enum to
/// replace the prior error-message-prefix routing
/// (`msg.starts_with("Unhandled request")` etc.) - that worked, but
/// silently coupled the dispatcher's routing decisions to the exact
/// wording of handler error strings, so a future handler whose
/// `Err` happened to start with a reserved prefix would have been
/// misrouted to the wrong wire error code.
#[derive(Debug)]
enum DispatchError {
    /// The request's `method` is not implemented by this server.
    /// Maps to [`lsp_server::ErrorCode::MethodNotFound`].
    MethodNotFound(String),
    /// A second `initialize` request reached the dispatcher. Per LSP
    /// 3.17 §Lifecycle, `initialize` MUST be sent exactly once; the
    /// first one is consumed by `server.rs::start_stdio` before the
    /// main loop runs, so any `initialize` reaching this dispatcher
    /// is a client-side protocol violation. Maps to
    /// [`lsp_server::ErrorCode::InvalidRequest`].
    DuplicateInitialize,
    /// A handler returned `Err(_)` for any other reason (parse error,
    /// IO failure, etc.). Maps to
    /// [`lsp_server::ErrorCode::InternalError`].
    Handler(String),
}

impl DispatchError {
    /// LSP wire error code for this dispatch failure.
    fn error_code(&self) -> lsp_server::ErrorCode {
        match self {
            Self::MethodNotFound(_) => lsp_server::ErrorCode::MethodNotFound,
            Self::DuplicateInitialize => lsp_server::ErrorCode::InvalidRequest,
            Self::Handler(_) => lsp_server::ErrorCode::InternalError,
        }
    }
}

impl std::fmt::Display for DispatchError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::MethodNotFound(method) => write!(f, "Unhandled request: {method}"),
            Self::DuplicateInitialize => write!(
                f,
                "initialize must be sent exactly once per LSP connection (LSP 3.17 \
                 §Lifecycle); this connection has already been initialized via \
                 server.rs::start_stdio."
            ),
            Self::Handler(msg) => f.write_str(msg),
        }
    }
}

/// State managed by the main loop.
pub struct MainLoopState {
    /// Virtual file system for open documents.
    pub vfs: Arc<RwLock<Vfs>>,
    /// Sender for outgoing LSP messages.
    pub sender: Sender<lsp_server::Message>,
    /// Cached diagnostics per file.
    pub diagnostics: HashMap<Uri, Vec<lsp_types::Diagnostic>>,
    /// Whether shutdown was requested.
    pub shutdown_requested: bool,
    /// Set by the `exit` notification handler. The main loop checks
    /// this after each event and breaks when it's `Some(_)`, returning
    /// the code from `run_main_loop_with_exit_action` so the caller
    /// (`server.rs::start_stdio` in production) can drain the writer
    /// thread via `io_threads.join()` BEFORE `process::exit`. Without
    /// this, the production exit_action was `process::exit(code)`
    /// directly - which terminates the process before the writer
    /// thread flushes the shutdown response queued in its channel.
    /// On a slow CI runner the writer can't keep up, the test
    /// observes only the initialize response on stdout, and
    /// `stdio_smoke` fails. See the `handle_notification` "exit"
    /// arm and `run_main_loop_with_exit_action`'s return-value
    /// documentation.
    pub pending_exit_code: Option<i32>,
    /// LSP position encoding negotiated at initialization (UTF-8 or
    /// UTF-16). Handler code emitting `Position`s must consult this
    /// so positions align with what the client expects.
    pub position_encoding: crate::handlers::utils::PositionEncoding,
    /// Full ledger state (loaded from journal file if configured).
    pub ledger_state: SharedLedgerState,
    /// Path to the journal file (if configured).
    pub journal_file: Option<PathBuf>,
    /// Channel for receiving results from background tasks.
    pub task_sender: Sender<TaskResult>,
    /// Receiver end of the task channel (used by run_main_loop).
    pub task_receiver: Receiver<TaskResult>,
    /// Channel for submitting jobs to the background worker thread.
    pub job_sender: Sender<BackgroundJob>,
    /// Per-instance revision counter for stale-result detection in
    /// `dispatch_async`. Pre-PR #1261 this was a process-wide static
    /// in `snapshot.rs`, which broke when multiple `MainLoopState`s
    /// shared a process: the integration test harness spawns many
    /// in-process LSP servers in parallel, and a `didChange` in test
    /// A would bump the revision such that test B's pending async
    /// result was silently discarded as stale even though B's world
    /// hadn't changed. Tests would then time out waiting for the
    /// dropped response. An `Arc<AtomicU64>` keeps clone-and-share
    /// cheap so worker closures can capture without borrowing
    /// `MainLoopState`.
    revision: Arc<std::sync::atomic::AtomicU64>,
    /// Action invoked when the `exit` notification arrives. Production
    /// wires this to [`std::process::exit`]; tests pass a no-op so the
    /// notification breaks the loop cleanly without terminating the
    /// cargo-test process. `FnOnce` because `exit` is the terminal
    /// notification of an LSP session.
    ///
    /// Defaults to `process::exit` so existing constructions continue
    /// to behave identically; override via [`Self::with_exit_action`]
    /// or [`run_main_loop_with_exit_action`].
    exit_action: Option<Box<dyn FnOnce(i32) + Send>>,
}

/// Default empty parse result for missing documents.
fn empty_parse_result() -> Arc<ParseResult> {
    Arc::new(parse(""))
}

impl MainLoopState {
    /// Create a new main loop state.
    pub fn new(sender: Sender<lsp_server::Message>, journal_file: Option<PathBuf>) -> Self {
        let ledger_state = new_shared_ledger_state();

        // Load journal file if configured
        if let Some(ref path) = journal_file {
            let mut state = ledger_state.write();
            if let Err(e) = state.load(path) {
                tracing::error!("Failed to load journal file: {e}");
            }
        }

        let (task_sender, task_receiver) = crossbeam_channel::unbounded();
        let (job_sender, job_receiver) = crossbeam_channel::unbounded::<BackgroundJob>();

        // Spawn a single persistent worker thread for background requests.
        // Using one thread avoids the overhead of thread-per-request while
        // still keeping the main loop unblocked. Jobs are processed FIFO;
        // stale results are discarded via revision-based cancellation.
        std::thread::Builder::new()
            .name("lsp-worker".into())
            .spawn(move || {
                for job in job_receiver {
                    job();
                }
            })
            .expect("failed to spawn LSP worker thread");

        Self {
            vfs: Arc::new(RwLock::new(Vfs::new())),
            sender,
            diagnostics: HashMap::new(),
            shutdown_requested: false,
            pending_exit_code: None,
            // Conservative default: UTF-16 (the LSP spec default).
            // `server.rs::run` overrides this with the negotiated
            // encoding after `initialize`. Construction without
            // initialize (e.g., in tests) gets the spec-safe value.
            position_encoding: crate::handlers::utils::PositionEncoding::Utf16,
            ledger_state,
            journal_file,
            task_sender,
            task_receiver,
            job_sender,
            revision: Arc::new(std::sync::atomic::AtomicU64::new(0)),
            // Production used to wire this to `process::exit(code)`,
            // which terminated before `io_threads.join()` could drain
            // the writer - losing the shutdown response on slow runners
            // (the stdio_smoke flake). The exit notification now
            // signals via `pending_exit_code` instead, and the loop
            // breaks normally; the caller then joins io_threads and
            // exits with the propagated code. `exit_action` is kept
            // for side effects (test harnesses use a no-op).
            exit_action: Some(Box::new(|_code| {})),
        }
    }

    /// Bump the per-instance revision counter. Called whenever the
    /// world state changes (didChange, didClose) so in-flight async
    /// handlers can detect they should drop their results.
    fn bump_revision(&self) -> u64 {
        self.revision
            .fetch_add(1, std::sync::atomic::Ordering::SeqCst)
            + 1
    }

    /// Replace the exit action. Returns `self` for chaining. The
    /// default action is a no-op (process termination, if any, is the
    /// caller's responsibility after `io_threads.join()`); tests pass a
    /// no-op (or a flag-set closure) to avoid terminating the test
    /// process when the `exit` notification arrives.
    #[must_use]
    pub fn with_exit_action<F>(mut self, action: F) -> Self
    where
        F: FnOnce(i32) + Send + 'static,
    {
        self.exit_action = Some(Box::new(action));
        self
    }

    /// Reload the journal file (e.g., after a file change).
    pub fn reload_journal(&mut self) {
        if let Some(ref path) = self.journal_file {
            let mut state = self.ledger_state.write();
            if let Err(e) = state.load(path) {
                tracing::error!("Failed to reload journal file: {e}");
            }
        }
    }

    /// Get document text and cached parse result for a URI.
    /// Uses cached parse result if available, avoiding re-parsing.
    fn get_document_data(&self, uri: &Uri) -> (String, Arc<ParseResult>) {
        if let Some(path) = uri_to_path(uri)
            && let Some((text, parse_result)) = self.vfs.write().get_document_data(&path)
        {
            return (text, parse_result);
        }
        (String::new(), empty_parse_result())
    }

    /// Handle an incoming event.
    pub fn handle_event(&mut self, event: Event) {
        match event {
            Event::Message(msg) => self.handle_message(msg),
            Event::Task(task_result) => {
                let response = match task_result.result {
                    Ok(value) => lsp_server::Response::new_ok(task_result.request_id, value),
                    Err(msg) => lsp_server::Response::new_err(
                        task_result.request_id,
                        lsp_server::ErrorCode::InternalError as i32,
                        msg,
                    ),
                };
                self.send(lsp_server::Message::Response(response));
            }
        }
    }

    /// Dispatch a request handler to the background worker thread.
    ///
    /// The handler closure receives no mutable state - it should capture
    /// any needed data (parse results, ledger state) before being moved.
    /// The result is sent back to the main loop as a `Task` event.
    ///
    /// Cancellation: the revision at dispatch time is captured. If the
    /// world state changes before the handler completes (e.g., user edits
    /// a document), the result is silently dropped instead of being sent.
    fn dispatch_async(
        &self,
        request_id: lsp_server::RequestId,
        handler: impl FnOnce() -> Result<serde_json::Value, String> + Send + 'static,
    ) {
        self.dispatch_async_inner(request_id, handler, true);
    }

    /// Same as [`Self::dispatch_async`] but skips the stale-result
    /// check. Use for handlers whose output does not depend on any
    /// world state (so "stale" and "fresh" produce the same answer).
    ///
    /// The staleness check exists to drop results computed against
    /// outdated parse / ledger snapshots; for a stateless handler
    /// (today: [`handle_code_lens_resolve`]'s defensive fallback,
    /// which does nothing more than fill `command` on a `None` lens)
    /// the check is pure overhead AND, critically, a correctness
    /// hazard when multiple `MainLoopState`s share a process - the
    /// revision counter is a process-wide `AtomicU64`, so parallel
    /// instances (e.g., the integration test harness) clobber each
    /// other's dispatch revisions and lose stateless results that
    /// have nothing to do with the world state.
    fn dispatch_async_unconditional(
        &self,
        request_id: lsp_server::RequestId,
        handler: impl FnOnce() -> Result<serde_json::Value, String> + Send + 'static,
    ) {
        self.dispatch_async_inner(request_id, handler, false);
    }

    fn dispatch_async_inner(
        &self,
        request_id: lsp_server::RequestId,
        handler: impl FnOnce() -> Result<serde_json::Value, String> + Send + 'static,
        check_staleness: bool,
    ) {
        let task_sender = self.task_sender.clone();
        // Capture the per-instance revision counter via Arc clone so
        // the worker can compare without borrowing `MainLoopState`.
        // Using the per-instance counter (not the global one in
        // `snapshot.rs`) is required for correctness when multiple
        // MainLoopStates share a process - see the `revision` field
        // rustdoc.
        let revision_arc = self.revision.clone();
        let dispatch_revision = if check_staleness {
            Some(revision_arc.load(std::sync::atomic::Ordering::SeqCst))
        } else {
            None
        };

        let _ = self.job_sender.send(Box::new(move || {
            let result = handler();

            // Drop stale results - if the world changed since dispatch,
            // the client will have sent a new request for fresh data.
            // Skipped for unconditional dispatch (stateless handlers).
            if let Some(rev) = dispatch_revision
                && revision_arc.load(std::sync::atomic::Ordering::SeqCst) != rev
            {
                tracing::debug!(
                    "Dropping stale result for request {:?} (revision changed)",
                    request_id
                );
                return;
            }

            // Ignore send errors - the main loop may have shut down
            let _ = task_sender.send(TaskResult { request_id, result });
        }));
    }

    /// Try to dispatch an expensive request to the background worker.
    ///
    /// Returns `true` if the request was dispatched (response will arrive
    /// as `Event::Task`), `false` if it should be handled synchronously.
    ///
    /// Data is eagerly snapshotted on the main thread (while locks are
    /// cheap), then the CPU-intensive handler runs on the worker thread.
    /// This avoids duplicating handler logic - the same handler functions
    /// are called from both sync and async paths.
    fn try_dispatch_async(&self, req: &lsp_server::Request) -> bool {
        match req.method.as_str() {
            // codeLens/resolve is now a no-op for every lens kind
            // emitted by `handle_code_lens` (since #1253, balance
            // lenses ship fully-resolved on the initial response).
            // The defensive fallback only fills in `command` when a
            // lens arrives with `command: None`, which no current
            // path produces. We keep the async dispatch wiring so a
            // future resolve-using lens kind that needs heavy work
            // can re-enable it cheaply, but we no longer snapshot
            // `parse_result` or clone the full ledger directives:
            // the fallback needs neither. Pre-#1253 those snapshots
            // each cost an O(N) deep clone on every resolve request.
            CodeLensResolve::METHOD => {
                let id = req.id.clone();
                let lens: CodeLens = match serde_json::from_value(req.params.clone()) {
                    Ok(l) => l,
                    Err(e) => {
                        // Use unconditional dispatch (stateless
                        // handler - see dispatch_async_unconditional).
                        self.dispatch_async_unconditional(id, move || Err(e.to_string()));
                        return true;
                    }
                };

                self.dispatch_async_unconditional(id, move || {
                    let resolved = handle_code_lens_resolve(lens);
                    serde_json::to_value(resolved).map_err(|e| e.to_string())
                });
                true
            }
            // semanticTokens/full tokenizes the entire document - CPU-bound.
            SemanticTokensFullRequest::METHOD => {
                let id = req.id.clone();
                let params: SemanticTokensParams = match serde_json::from_value(req.params.clone())
                {
                    Ok(p) => p,
                    Err(e) => {
                        self.dispatch_async(id, move || Err(e.to_string()));
                        return true;
                    }
                };

                // Snapshot data eagerly
                let uri = &params.text_document.uri;
                let (text, parse_result) = self.get_document_data(uri);
                // Capture the negotiated encoding by value so the
                // worker closure (which loses access to `self`) emits
                // semantic tokens in the right wire encoding.
                let encoding = self.position_encoding;

                self.dispatch_async(id, move || {
                    let response = handle_semantic_tokens(&params, &text, &parse_result, encoding);
                    serde_json::to_value(response).map_err(|e| e.to_string())
                });
                true
            }
            _ => false,
        }
    }

    /// Handle an LSP message.
    fn handle_message(&mut self, msg: Message) {
        match msg {
            Message::Request(req) => self.handle_request(req),
            Message::Notification(notif) => self.handle_notification(notif),
            Message::Response(_resp) => {
                // We don't currently send requests to the client
            }
        }
    }

    /// Handle an LSP request (expects response).
    ///
    /// Most read-only requests are dispatched to a background thread to keep
    /// the main loop responsive. Requests that mutate state (initialize,
    /// shutdown) or need ordering guarantees run synchronously.
    fn handle_request(&mut self, req: lsp_server::Request) {
        let id = req.id.clone();

        // Check for async-dispatchable requests first.
        // These are read-only and can safely run off the main thread.
        if self.try_dispatch_async(&req) {
            return; // Response will come back as Event::Task
        }

        // Send response, routed through the typed `DispatchError`
        // (see the enum's rustdoc for the rationale - round-20
        // replaces the prior error-message-prefix routing).
        let response = match self.dispatch_sync(req) {
            Ok(value) => lsp_server::Response::new_ok(id, value),
            Err(err) => lsp_server::Response::new_err(id, err.error_code() as i32, err.to_string()),
        };

        self.send(lsp_server::Message::Response(response));
    }

    /// Synchronous request dispatch. Returns the handler's JSON
    /// response, or a typed [`DispatchError`].
    ///
    /// Each match arm either handles the request inline (Shutdown,
    /// Initialize) or delegates to a per-method handler that returns
    /// `Result<Value, String>`; the inner `String` is wrapped via
    /// `DispatchError::Handler` on the way out, keeping the handler
    /// signatures unchanged.
    fn dispatch_sync(
        &mut self,
        req: lsp_server::Request,
    ) -> Result<serde_json::Value, DispatchError> {
        // Initialize is special: a second `initialize` reaching this
        // dispatcher is a protocol violation per LSP 3.17 §Lifecycle.
        // Parse the params to surface a malformed-payload error if
        // present, then emit the structured `DuplicateInitialize`.
        if req.method == Initialize::METHOD {
            let _params: InitializeParams = serde_json::from_value(req.params)
                .map_err(|e| DispatchError::Handler(e.to_string()))?;
            return Err(DispatchError::DuplicateInitialize);
        }

        let method = req.method.clone();
        let inner: Result<serde_json::Value, String> = match method.as_str() {
            Shutdown::METHOD => {
                self.shutdown_requested = true;
                Ok(serde_json::Value::Null)
            }
            Completion::METHOD => self.handle_completion_request(req),
            GotoDefinition::METHOD => self.handle_goto_definition_request(req),
            References::METHOD => self.handle_references_request(req),
            HoverRequest::METHOD => self.handle_hover_request(req),
            DocumentSymbolRequest::METHOD => self.handle_document_symbols_request(req),
            SemanticTokensFullDeltaRequest::METHOD => {
                self.handle_semantic_tokens_delta_request(req)
            }
            SemanticTokensRangeRequest::METHOD => self.handle_semantic_tokens_range_request(req),
            CodeActionRequest::METHOD => self.handle_code_action_request(req),
            CodeActionResolveRequest::METHOD => self.handle_code_action_resolve_request(req),
            WorkspaceSymbolRequest::METHOD => self.handle_workspace_symbol_request(req),
            PrepareRenameRequest::METHOD => self.handle_prepare_rename_request(req),
            Rename::METHOD => self.handle_rename_request(req),
            Formatting::METHOD => self.handle_formatting_request(req),
            RangeFormatting::METHOD => self.handle_range_formatting_request(req),
            DocumentLinkRequest::METHOD => self.handle_document_link_request(req),
            DocumentLinkResolve::METHOD => self.handle_document_link_resolve_request(req),
            InlayHintRequest::METHOD => self.handle_inlay_hint_request(req),
            InlayHintResolveRequest::METHOD => self.handle_inlay_hint_resolve_request(req),
            SelectionRangeRequest::METHOD => self.handle_selection_range_request(req),
            FoldingRangeRequest::METHOD => self.handle_folding_range_request(req),
            TypeHierarchyPrepare::METHOD => self.handle_prepare_type_hierarchy_request(req),
            TypeHierarchySupertypes::METHOD => self.handle_type_hierarchy_supertypes_request(req),
            TypeHierarchySubtypes::METHOD => self.handle_type_hierarchy_subtypes_request(req),
            DocumentHighlightRequest::METHOD => self.handle_document_highlight_request(req),
            LinkedEditingRange::METHOD => self.handle_linked_editing_range_request(req),
            OnTypeFormatting::METHOD => self.handle_on_type_formatting_request(req),
            CodeLensRequest::METHOD => self.handle_code_lens_request(req),
            DocumentColor::METHOD => self.handle_document_color_request(req),
            ColorPresentationRequest::METHOD => self.handle_color_presentation_request(req),
            GotoDeclaration::METHOD => self.handle_goto_declaration_request(req),
            CallHierarchyPrepare::METHOD => self.handle_prepare_call_hierarchy_request(req),
            CallHierarchyIncomingCalls::METHOD => self.handle_incoming_calls_request(req),
            CallHierarchyOutgoingCalls::METHOD => self.handle_outgoing_calls_request(req),
            SignatureHelpRequest::METHOD => self.handle_signature_help_request(req),
            ExecuteCommand::METHOD => self.handle_execute_command_request(req),
            ResolveCompletionItem::METHOD => self.handle_completion_resolve_request(req),
            _ => {
                tracing::warn!("Unhandled request: {method}");
                return Err(DispatchError::MethodNotFound(method));
            }
        };
        inner.map_err(DispatchError::Handler)
    }

    /// Handle the textDocument/completion request.
    fn handle_completion_request(
        &self,
        req: lsp_server::Request,
    ) -> Result<serde_json::Value, String> {
        let params: CompletionParams =
            serde_json::from_value(req.params).map_err(|e| e.to_string())?;

        let uri = &params.text_document_position.text_document.uri;
        let (text, parse_result) = self.get_document_data(uri);

        // Get ledger state for multi-file completions
        let ledger_guard = self.ledger_state.read();
        let ledger_state = if ledger_guard.ledger().is_some() {
            Some(&*ledger_guard)
        } else {
            None
        };

        let response = handle_completion(
            &params,
            &text,
            &parse_result,
            ledger_state,
            self.position_encoding,
        );

        serde_json::to_value(response).map_err(|e| e.to_string())
    }

    /// Handle the textDocument/definition request.
    fn handle_goto_definition_request(
        &self,
        req: lsp_server::Request,
    ) -> Result<serde_json::Value, String> {
        let params: GotoDefinitionParams =
            serde_json::from_value(req.params).map_err(|e| e.to_string())?;

        let uri = &params.text_document_position_params.text_document.uri;
        let (text, parse_result) = self.get_document_data(uri);

        // Ledger state for cross-file (`include`d) account definitions.
        let ledger_guard = self.ledger_state.read();
        let ledger_state = if ledger_guard.ledger().is_some() {
            Some(&*ledger_guard)
        } else {
            None
        };

        let response = handle_goto_definition(
            &params,
            &text,
            &parse_result,
            ledger_state,
            uri,
            self.position_encoding,
        );

        serde_json::to_value(response).map_err(|e| e.to_string())
    }

    /// Handle the textDocument/references request.
    fn handle_references_request(
        &self,
        req: lsp_server::Request,
    ) -> Result<serde_json::Value, String> {
        let params: ReferenceParams =
            serde_json::from_value(req.params).map_err(|e| e.to_string())?;

        let uri = &params.text_document_position.text_document.uri;
        let (text, parse_result) = self.get_document_data(uri);

        let response =
            handle_references(&params, &text, &parse_result, uri, self.position_encoding);

        serde_json::to_value(response).map_err(|e| e.to_string())
    }

    /// Handle the textDocument/hover request.
    fn handle_hover_request(&self, req: lsp_server::Request) -> Result<serde_json::Value, String> {
        let params: HoverParams = serde_json::from_value(req.params).map_err(|e| e.to_string())?;

        let uri = &params.text_document_position_params.text_document.uri;
        let (text, parse_result) = self.get_document_data(uri);

        // Ledger state for cross-file (`include`d) account resolution.
        let ledger_guard = self.ledger_state.read();
        let ledger_state = if ledger_guard.ledger().is_some() {
            Some(&*ledger_guard)
        } else {
            None
        };

        let response = handle_hover(
            &params,
            &text,
            &parse_result,
            ledger_state,
            self.position_encoding,
        );

        serde_json::to_value(response).map_err(|e| e.to_string())
    }

    /// Handle the textDocument/documentSymbol request.
    fn handle_document_symbols_request(
        &self,
        req: lsp_server::Request,
    ) -> Result<serde_json::Value, String> {
        let params: DocumentSymbolParams =
            serde_json::from_value(req.params).map_err(|e| e.to_string())?;

        let uri = &params.text_document.uri;
        let (text, parse_result) = self.get_document_data(uri);

        let response =
            handle_document_symbols(&params, &text, &parse_result, self.position_encoding);

        serde_json::to_value(response).map_err(|e| e.to_string())
    }

    /// Handle the textDocument/semanticTokens/full/delta request.
    fn handle_semantic_tokens_delta_request(
        &self,
        req: lsp_server::Request,
    ) -> Result<serde_json::Value, String> {
        let params: SemanticTokensDeltaParams =
            serde_json::from_value(req.params).map_err(|e| e.to_string())?;

        let uri = &params.text_document.uri;
        let (text, parse_result) = self.get_document_data(uri);

        // Note: For a full implementation, we would store previous tokens by result_id
        // and pass them to handle_semantic_tokens_delta. For now, pass None to always
        // return full tokens as a delta.
        let response = handle_semantic_tokens_delta(
            &params,
            &text,
            &parse_result,
            None,
            self.position_encoding,
        );

        serde_json::to_value(response).map_err(|e| e.to_string())
    }

    /// Handle the textDocument/semanticTokens/range request.
    fn handle_semantic_tokens_range_request(
        &self,
        req: lsp_server::Request,
    ) -> Result<serde_json::Value, String> {
        let params: SemanticTokensRangeParams =
            serde_json::from_value(req.params).map_err(|e| e.to_string())?;

        let uri = &params.text_document.uri;
        let (text, parse_result) = self.get_document_data(uri);

        let response =
            handle_semantic_tokens_range(&params, &text, &parse_result, self.position_encoding);

        serde_json::to_value(response).map_err(|e| e.to_string())
    }

    /// Handle the textDocument/codeAction request.
    fn handle_code_action_request(
        &self,
        req: lsp_server::Request,
    ) -> Result<serde_json::Value, String> {
        let params: CodeActionParams =
            serde_json::from_value(req.params).map_err(|e| e.to_string())?;

        let uri = &params.text_document.uri;
        let (text, parse_result) = self.get_document_data(uri);

        let response = handle_code_actions(&params, &text, &parse_result, self.position_encoding);

        serde_json::to_value(response).map_err(|e| e.to_string())
    }

    /// Handle the codeAction/resolve request.
    fn handle_code_action_resolve_request(
        &self,
        req: lsp_server::Request,
    ) -> Result<serde_json::Value, String> {
        let action: CodeAction = serde_json::from_value(req.params).map_err(|e| e.to_string())?;

        // Get the document URI from the action's data
        let uri: Uri = if let Some(data) = &action.data {
            data.get("uri")
                .and_then(|v| v.as_str())
                .and_then(|s| s.parse().ok())
                .unwrap_or_else(|| "file:///unknown".parse().unwrap())
        } else {
            "file:///unknown".parse().unwrap()
        };

        let (text, parse_result) = self.get_document_data(&uri);

        let resolved =
            handle_code_action_resolve(action, &text, &parse_result, &uri, self.position_encoding);

        serde_json::to_value(resolved).map_err(|e| e.to_string())
    }

    /// Handle the workspace/symbol request.
    fn handle_workspace_symbol_request(
        &self,
        req: lsp_server::Request,
    ) -> Result<serde_json::Value, String> {
        let params: WorkspaceSymbolParams =
            serde_json::from_value(req.params).map_err(|e| e.to_string())?;

        // Collect all open documents with cached parse results
        let mut vfs = self.vfs.write();
        let documents: Vec<_> = vfs
            .iter_with_parse()
            .map(|(path, content, parse_result)| {
                let uri_str = format!("file://{}", path.display());
                let uri: Uri = uri_str
                    .parse()
                    .unwrap_or_else(|_| "file:///".parse().unwrap());
                (uri, content, parse_result)
            })
            .collect();

        let response = handle_workspace_symbols(&params, &documents, self.position_encoding);

        serde_json::to_value(response).map_err(|e| e.to_string())
    }

    /// Handle the textDocument/prepareRename request.
    fn handle_prepare_rename_request(
        &self,
        req: lsp_server::Request,
    ) -> Result<serde_json::Value, String> {
        let params: TextDocumentPositionParams =
            serde_json::from_value(req.params).map_err(|e| e.to_string())?;

        let uri = &params.text_document.uri;
        let (text, parse_result) = self.get_document_data(uri);

        let response = handle_prepare_rename(&params, &text, &parse_result, self.position_encoding);

        serde_json::to_value(response).map_err(|e| e.to_string())
    }

    /// Handle the textDocument/rename request.
    fn handle_rename_request(&self, req: lsp_server::Request) -> Result<serde_json::Value, String> {
        let params: RenameParams = serde_json::from_value(req.params).map_err(|e| e.to_string())?;

        let uri = &params.text_document_position.text_document.uri;
        let (text, parse_result) = self.get_document_data(uri);

        let response = handle_rename(&params, &text, &parse_result, self.position_encoding);

        serde_json::to_value(response).map_err(|e| e.to_string())
    }

    /// Handle the textDocument/formatting request.
    fn handle_formatting_request(
        &self,
        req: lsp_server::Request,
    ) -> Result<serde_json::Value, String> {
        let params: DocumentFormattingParams =
            serde_json::from_value(req.params).map_err(|e| e.to_string())?;

        let uri = &params.text_document.uri;
        let (text, parse_result) = self.get_document_data(uri);

        let response = handle_formatting(&params, &text, &parse_result, self.position_encoding);

        serde_json::to_value(response).map_err(|e| e.to_string())
    }

    /// Handle the textDocument/foldingRange request.
    fn handle_folding_range_request(
        &self,
        req: lsp_server::Request,
    ) -> Result<serde_json::Value, String> {
        let params: FoldingRangeParams =
            serde_json::from_value(req.params).map_err(|e| e.to_string())?;

        let uri = &params.text_document.uri;
        let (text, parse_result) = self.get_document_data(uri);

        let response = handle_folding_ranges(&params, &text, &parse_result, self.position_encoding);

        serde_json::to_value(response).map_err(|e| e.to_string())
    }

    /// Handle the textDocument/rangeFormatting request.
    fn handle_range_formatting_request(
        &self,
        req: lsp_server::Request,
    ) -> Result<serde_json::Value, String> {
        let params: DocumentRangeFormattingParams =
            serde_json::from_value(req.params).map_err(|e| e.to_string())?;

        let uri = &params.text_document.uri;
        let (text, parse_result) = self.get_document_data(uri);

        let response =
            handle_range_formatting(&params, &text, &parse_result, self.position_encoding);

        serde_json::to_value(response).map_err(|e| e.to_string())
    }

    /// Handle the textDocument/documentLink request.
    fn handle_document_link_request(
        &self,
        req: lsp_server::Request,
    ) -> Result<serde_json::Value, String> {
        let params: DocumentLinkParams =
            serde_json::from_value(req.params).map_err(|e| e.to_string())?;

        let uri = &params.text_document.uri;
        let (text, parse_result) = self.get_document_data(uri);

        let response = handle_document_links(&params, &text, &parse_result, self.position_encoding);

        serde_json::to_value(response).map_err(|e| e.to_string())
    }

    /// Handle the documentLink/resolve request.
    fn handle_document_link_resolve_request(
        &self,
        req: lsp_server::Request,
    ) -> Result<serde_json::Value, String> {
        let link: DocumentLink = serde_json::from_value(req.params).map_err(|e| e.to_string())?;

        let resolved = handle_document_link_resolve(link);

        serde_json::to_value(resolved).map_err(|e| e.to_string())
    }

    /// Handle the textDocument/inlayHint request.
    fn handle_inlay_hint_request(
        &self,
        req: lsp_server::Request,
    ) -> Result<serde_json::Value, String> {
        let params: InlayHintParams =
            serde_json::from_value(req.params).map_err(|e| e.to_string())?;

        let uri = &params.text_document.uri;
        let (text, parse_result) = self.get_document_data(uri);

        let response = handle_inlay_hints(&params, &text, &parse_result, self.position_encoding);

        serde_json::to_value(response).map_err(|e| e.to_string())
    }

    /// Handle the inlayHint/resolve request.
    fn handle_inlay_hint_resolve_request(
        &self,
        req: lsp_server::Request,
    ) -> Result<serde_json::Value, String> {
        let hint: InlayHint = serde_json::from_value(req.params).map_err(|e| e.to_string())?;

        // Get the document URI from the hint's data field
        let uri: Uri = if let Some(data) = &hint.data {
            data.get("uri")
                .and_then(|v| v.as_str())
                .and_then(|s| s.parse().ok())
                .unwrap_or_else(|| "file:///unknown".parse().unwrap())
        } else {
            "file:///unknown".parse().unwrap()
        };

        let (_text, parse_result) = self.get_document_data(&uri);
        let resolved = handle_inlay_hint_resolve(hint, &parse_result);

        serde_json::to_value(resolved).map_err(|e| e.to_string())
    }

    /// Handle the textDocument/selectionRange request.
    fn handle_selection_range_request(
        &self,
        req: lsp_server::Request,
    ) -> Result<serde_json::Value, String> {
        let params: SelectionRangeParams =
            serde_json::from_value(req.params).map_err(|e| e.to_string())?;

        let uri = &params.text_document.uri;
        let (text, parse_result) = self.get_document_data(uri);

        // CST handle comes from the cached ParseResult via
        // `parse_result.syntax_root`; no per-request re-parse.
        let response =
            handle_selection_range(&params, &text, &parse_result, self.position_encoding);

        serde_json::to_value(response).map_err(|e| e.to_string())
    }

    /// Handle the textDocument/prepareTypeHierarchy request.
    fn handle_prepare_type_hierarchy_request(
        &self,
        req: lsp_server::Request,
    ) -> Result<serde_json::Value, String> {
        let params: TypeHierarchyPrepareParams =
            serde_json::from_value(req.params).map_err(|e| e.to_string())?;

        let uri = &params.text_document_position_params.text_document.uri;
        let (text, parse_result) = self.get_document_data(uri);

        let response = handle_prepare_type_hierarchy(
            &params,
            &text,
            &parse_result,
            uri,
            self.position_encoding,
        );

        serde_json::to_value(response).map_err(|e| e.to_string())
    }

    /// Handle the typeHierarchy/supertypes request.
    fn handle_type_hierarchy_supertypes_request(
        &self,
        req: lsp_server::Request,
    ) -> Result<serde_json::Value, String> {
        let params: TypeHierarchySupertypesParams =
            serde_json::from_value(req.params).map_err(|e| e.to_string())?;

        let uri = &params.item.uri;
        let (text, parse_result) = self.get_document_data(uri);

        let response =
            handle_supertypes(&params, &text, &parse_result, uri, self.position_encoding);

        serde_json::to_value(response).map_err(|e| e.to_string())
    }

    /// Handle the typeHierarchy/subtypes request.
    fn handle_type_hierarchy_subtypes_request(
        &self,
        req: lsp_server::Request,
    ) -> Result<serde_json::Value, String> {
        let params: TypeHierarchySubtypesParams =
            serde_json::from_value(req.params).map_err(|e| e.to_string())?;

        let uri = &params.item.uri;
        let (text, parse_result) = self.get_document_data(uri);

        let response = handle_subtypes(&params, &text, &parse_result, uri, self.position_encoding);

        serde_json::to_value(response).map_err(|e| e.to_string())
    }

    /// Handle the textDocument/documentHighlight request.
    fn handle_document_highlight_request(
        &self,
        req: lsp_server::Request,
    ) -> Result<serde_json::Value, String> {
        let params: DocumentHighlightParams =
            serde_json::from_value(req.params).map_err(|e| e.to_string())?;

        let uri = &params.text_document_position_params.text_document.uri;
        let (text, parse_result) = self.get_document_data(uri);

        let response =
            handle_document_highlight(&params, &text, &parse_result, self.position_encoding);

        serde_json::to_value(response).map_err(|e| e.to_string())
    }

    /// Handle the textDocument/linkedEditingRange request.
    fn handle_linked_editing_range_request(
        &self,
        req: lsp_server::Request,
    ) -> Result<serde_json::Value, String> {
        let params: LinkedEditingRangeParams =
            serde_json::from_value(req.params).map_err(|e| e.to_string())?;

        let uri = &params.text_document_position_params.text_document.uri;
        let (text, parse_result) = self.get_document_data(uri);

        let response =
            handle_linked_editing_range(&params, &text, &parse_result, self.position_encoding);

        serde_json::to_value(response).map_err(|e| e.to_string())
    }

    /// Handle the textDocument/onTypeFormatting request.
    fn handle_on_type_formatting_request(
        &self,
        req: lsp_server::Request,
    ) -> Result<serde_json::Value, String> {
        let params: DocumentOnTypeFormattingParams =
            serde_json::from_value(req.params).map_err(|e| e.to_string())?;

        let uri = &params.text_document_position.text_document.uri;

        // Get document content from VFS (on-type formatting doesn't need parse result)
        let text = if let Some(path) = uri_to_path(uri) {
            self.vfs.read().get_content(&path).unwrap_or_default()
        } else {
            String::new()
        };

        let response = handle_on_type_formatting(&params, &text, self.position_encoding);

        serde_json::to_value(response).map_err(|e| e.to_string())
    }

    /// Handle the textDocument/codeLens request.
    fn handle_code_lens_request(
        &self,
        req: lsp_server::Request,
    ) -> Result<serde_json::Value, String> {
        let params: CodeLensParams =
            serde_json::from_value(req.params).map_err(|e| e.to_string())?;

        let uri = &params.text_document.uri;
        let (text, parse_result) = self.get_document_data(uri);

        // The balance lens reads the validator's last-computed verdict
        // for this URI from `self.diagnostics` (#1264). Pre-#1264 we
        // snapshotted `ledger_state` so the lens could run its own
        // evaluator; that evaluator dropped plugins (effective_date,
        // lazy_balance, ...) and silently disagreed with `rledger check`
        // on every ledger that used them. The new lens consults the
        // diagnostic cache instead - diagnostics ARE the validator's
        // verdict after the full pipeline. None means cold start
        // (no `publish_diagnostics` for this URI yet); the lens renders
        // a neutral title and never claims a verdict it can't back up.
        let cached_diagnostics = self.diagnostics.get(uri).map(Vec::as_slice);

        let response = handle_code_lens(
            &params,
            &text,
            &parse_result,
            cached_diagnostics,
            self.position_encoding,
        );

        serde_json::to_value(response).map_err(|e| e.to_string())
    }

    /// Handle the textDocument/documentColor request.
    fn handle_document_color_request(
        &self,
        req: lsp_server::Request,
    ) -> Result<serde_json::Value, String> {
        let params: DocumentColorParams =
            serde_json::from_value(req.params).map_err(|e| e.to_string())?;

        let uri = &params.text_document.uri;
        let (text, parse_result) = self.get_document_data(uri);

        let response = handle_document_color(&params, &text, &parse_result, self.position_encoding);

        serde_json::to_value(response).map_err(|e| e.to_string())
    }

    /// Handle the textDocument/colorPresentation request.
    fn handle_color_presentation_request(
        &self,
        req: lsp_server::Request,
    ) -> Result<serde_json::Value, String> {
        let params: ColorPresentationParams =
            serde_json::from_value(req.params).map_err(|e| e.to_string())?;

        // Handle color presentation
        let response = handle_color_presentation(&params);

        serde_json::to_value(response).map_err(|e| e.to_string())
    }

    /// Handle the textDocument/declaration request.
    fn handle_goto_declaration_request(
        &self,
        req: lsp_server::Request,
    ) -> Result<serde_json::Value, String> {
        let params: GotoDefinitionParams =
            serde_json::from_value(req.params).map_err(|e| e.to_string())?;

        let uri = &params.text_document_position_params.text_document.uri;
        let (text, parse_result) = self.get_document_data(uri);

        // Ledger state for cross-file (`include`d) account declarations.
        let ledger_guard = self.ledger_state.read();
        let ledger_state = if ledger_guard.ledger().is_some() {
            Some(&*ledger_guard)
        } else {
            None
        };

        // Handle go-to-declaration (same as definition for Beancount)
        let response = handle_goto_declaration(
            &params,
            &text,
            &parse_result,
            ledger_state,
            uri,
            self.position_encoding,
        );

        serde_json::to_value(response).map_err(|e| e.to_string())
    }

    /// Handle the textDocument/prepareCallHierarchy request.
    fn handle_prepare_call_hierarchy_request(
        &self,
        req: lsp_server::Request,
    ) -> Result<serde_json::Value, String> {
        let params: CallHierarchyPrepareParams =
            serde_json::from_value(req.params).map_err(|e| e.to_string())?;

        let uri = &params.text_document_position_params.text_document.uri;
        let (text, parse_result) = self.get_document_data(uri);

        let response = handle_prepare_call_hierarchy(
            &params,
            &text,
            &parse_result,
            uri,
            self.position_encoding,
        );

        serde_json::to_value(response).map_err(|e| e.to_string())
    }

    /// Handle the callHierarchy/incomingCalls request.
    fn handle_incoming_calls_request(
        &self,
        req: lsp_server::Request,
    ) -> Result<serde_json::Value, String> {
        let params: CallHierarchyIncomingCallsParams =
            serde_json::from_value(req.params).map_err(|e| e.to_string())?;

        let uri = &params.item.uri;
        let (text, parse_result) = self.get_document_data(uri);

        let response =
            handle_incoming_calls(&params, &text, &parse_result, uri, self.position_encoding);

        serde_json::to_value(response).map_err(|e| e.to_string())
    }

    /// Handle the callHierarchy/outgoingCalls request.
    fn handle_outgoing_calls_request(
        &self,
        req: lsp_server::Request,
    ) -> Result<serde_json::Value, String> {
        let params: CallHierarchyOutgoingCallsParams =
            serde_json::from_value(req.params).map_err(|e| e.to_string())?;

        let uri = &params.item.uri;
        let (text, parse_result) = self.get_document_data(uri);

        let response =
            handle_outgoing_calls(&params, &text, &parse_result, uri, self.position_encoding);

        serde_json::to_value(response).map_err(|e| e.to_string())
    }

    /// Handle the textDocument/signatureHelp request.
    fn handle_signature_help_request(
        &self,
        req: lsp_server::Request,
    ) -> Result<serde_json::Value, String> {
        let params: SignatureHelpParams =
            serde_json::from_value(req.params).map_err(|e| e.to_string())?;

        let uri = &params.text_document_position_params.text_document.uri;

        // Get document content from VFS
        let text = if let Some(path) = uri_to_path(uri) {
            self.vfs.read().get_content(&path).unwrap_or_default()
        } else {
            String::new()
        };

        // Handle signature help (doesn't need parse result)
        let response = handle_signature_help(&params, &text, self.position_encoding);

        serde_json::to_value(response).map_err(|e| e.to_string())
    }

    /// Handle the workspace/executeCommand request.
    fn handle_execute_command_request(
        &self,
        req: lsp_server::Request,
    ) -> Result<serde_json::Value, String> {
        let params: ExecuteCommandParams =
            serde_json::from_value(req.params).map_err(|e| e.to_string())?;

        // Try to get URI from command arguments first
        let uri_from_args: Option<Uri> = params
            .arguments
            .first()
            .and_then(|arg| arg.get("uri"))
            .and_then(|v| v.as_str())
            .and_then(|s| s.parse().ok());

        if let Some(uri) = uri_from_args {
            let (text, parse_result) = self.get_document_data(&uri);
            let result =
                handle_execute_command(&params, &text, &parse_result, &uri, self.position_encoding);
            self.send_show_message(result.show_message);
            return Ok(result.response.unwrap_or(serde_json::Value::Null));
        }

        // Fall back to first open document (legacy behavior)
        let first_path = self.vfs.read().paths().next().cloned();
        let path = match first_path {
            Some(p) => p,
            None => {
                return Ok(serde_json::json!({
                    "error": "No document open"
                }));
            }
        };

        // Convert path to URI
        #[cfg(not(windows))]
        let uri: Uri = format!("file://{}", path.display())
            .parse()
            .map_err(|e| format!("{:?}", e))?;
        #[cfg(windows)]
        let uri: Uri = format!("file:///{}", path.display())
            .parse()
            .map_err(|e| format!("{:?}", e))?;

        let (text, parse_result) = self.get_document_data(&uri);
        let result =
            handle_execute_command(&params, &text, &parse_result, &uri, self.position_encoding);
        self.send_show_message(result.show_message);
        Ok(result.response.unwrap_or(serde_json::Value::Null))
    }

    /// Send a `window/showMessage` notification, if any.
    fn send_show_message(&self, params: Option<lsp_types::ShowMessageParams>) {
        let Some(params) = params else { return };
        let notif = lsp_server::Notification::new(
            <lsp_types::notification::ShowMessage as lsp_types::notification::Notification>::METHOD
                .to_string(),
            params,
        );
        self.send(lsp_server::Message::Notification(notif));
    }

    /// Handle the completionItem/resolve request.
    fn handle_completion_resolve_request(
        &self,
        req: lsp_server::Request,
    ) -> Result<serde_json::Value, String> {
        let item: CompletionItem = serde_json::from_value(req.params).map_err(|e| e.to_string())?;

        // Try to get URI from the completion item's data field
        let uri: Uri = if let Some(data) = &item.data {
            data.get("uri")
                .and_then(|v| v.as_str())
                .and_then(|s| s.parse().ok())
                .unwrap_or_else(|| "file:///unknown".parse().unwrap())
        } else {
            "file:///unknown".parse().unwrap()
        };

        let (_text, parse_result) = self.get_document_data(&uri);

        // Resolve the detail (balances, transaction counts, price
        // history) against the full ledger when a journalFile is
        // configured — the loaded ledger spans every included file, so
        // the popup reflects whole-ledger totals instead of just the
        // file the cursor is in. Falls back to the current file's
        // directives when no ledger is loaded. Mirrors how
        // `handle_completion_request` consults `ledger_state`, and
        // keeps the detail consistent with `hover` (issue #1297).
        let ledger_guard = self.ledger_state.read();
        let directives = ledger_guard
            .directives()
            .unwrap_or_else(|| parse_result.directives.as_slice());
        let resolved = handle_completion_resolve(item, directives);

        serde_json::to_value(resolved).map_err(|e| e.to_string())
    }

    /// Handle an LSP notification (no response expected).
    fn handle_notification(&mut self, notif: lsp_server::Notification) {
        // Notifications are handled synchronously - this is critical for correctness
        match notif.method.as_str() {
            DidOpenTextDocument::METHOD => {
                if let Ok(params) =
                    serde_json::from_value::<lsp_types::DidOpenTextDocumentParams>(notif.params)
                {
                    self.on_did_open(params);
                }
            }
            DidChangeTextDocument::METHOD => {
                if let Ok(params) =
                    serde_json::from_value::<lsp_types::DidChangeTextDocumentParams>(notif.params)
                {
                    self.on_did_change(params);
                }
            }
            DidCloseTextDocument::METHOD => {
                if let Ok(params) =
                    serde_json::from_value::<lsp_types::DidCloseTextDocumentParams>(notif.params)
                {
                    self.on_did_close(params);
                }
            }
            DidChangeWatchedFiles::METHOD => {
                if let Ok(params) =
                    serde_json::from_value::<lsp_types::DidChangeWatchedFilesParams>(notif.params)
                {
                    self.on_did_change_watched_files(params);
                }
            }
            "initialized" => {
                tracing::info!("Client initialized");
                // Register for file watching after initialization
                self.register_file_watchers();
            }
            "exit" => {
                tracing::info!("Exit notification received");
                let code = if self.shutdown_requested { 0 } else { 1 };
                // Signal the main loop to break with this code; the
                // caller will drain the writer thread before exiting.
                // See `pending_exit_code` field rustdoc.
                self.pending_exit_code = Some(code);
                // Invoke any caller-supplied side effect (test harnesses
                // pass a no-op; production passes a no-op too post-fix
                // because the actual process::exit is now done by the
                // outer caller AFTER io_threads.join()).
                if let Some(action) = self.exit_action.take() {
                    action(code);
                }
            }
            _ => {
                tracing::debug!("Unhandled notification: {}", notif.method);
            }
        }
    }

    /// Handle textDocument/didOpen notification.
    fn on_did_open(&mut self, params: lsp_types::DidOpenTextDocumentParams) {
        let uri = params.text_document.uri;
        let text = params.text_document.text;
        let version = params.text_document.version;

        tracing::info!("Document opened: {}", uri.as_str());

        // Store in VFS
        if let Some(path) = uri_to_path(&uri) {
            self.vfs.write().open(path, text.clone(), version);
        }

        // Bump revision (invalidates any in-flight requests)
        self.bump_revision();

        // Compute and publish diagnostics
        self.publish_diagnostics(&uri, &text);
    }

    /// Handle textDocument/didChange notification.
    fn on_did_change(&mut self, params: lsp_types::DidChangeTextDocumentParams) {
        let uri = params.text_document.uri;
        let version = params.text_document.version;

        // For full sync, take the last change (which is the full content)
        if let Some(change) = params.content_changes.into_iter().last() {
            let text = change.text;

            tracing::debug!("Document changed: {}", uri.as_str());

            // Update VFS
            if let Some(path) = uri_to_path(&uri) {
                self.vfs.write().update(&path, text.clone(), version);
            }

            // Bump revision
            self.bump_revision();

            // Recompute diagnostics
            self.publish_diagnostics(&uri, &text);
        }
    }

    /// Handle textDocument/didClose notification.
    fn on_did_close(&mut self, params: lsp_types::DidCloseTextDocumentParams) {
        let uri = params.text_document.uri;

        tracing::info!("Document closed: {}", uri.as_str());

        // Remove from VFS
        if let Some(path) = uri_to_path(&uri) {
            self.vfs.write().close(&path);
        }

        // Clear diagnostics
        self.diagnostics.remove(&uri);
        self.send_diagnostics(&uri, vec![]);
    }

    /// Handle workspace/didChangeWatchedFiles notification.
    fn on_did_change_watched_files(&mut self, params: lsp_types::DidChangeWatchedFilesParams) {
        tracing::info!("Watched files changed: {} files", params.changes.len());

        let mut should_reload_journal = false;
        let mut should_revalidate = false;

        for change in params.changes {
            tracing::debug!("File {:?}: {:?}", change.uri.as_str(), change.typ);

            // Check if the changed file is part of our journal
            if let Some(path) = uri_to_path(&change.uri) {
                let ledger_guard = self.ledger_state.read();
                if ledger_guard.contains_file(&path) {
                    should_reload_journal = true;
                }
            }

            // If a .beancount or .bean file changed externally, mark for revalidation
            if change.uri.as_str().ends_with(".beancount") || change.uri.as_str().ends_with(".bean")
            {
                should_revalidate = true;
            }
        }

        // Reload the journal if any of its files changed
        if should_reload_journal {
            tracing::info!("Reloading journal due to external file changes");
            self.reload_journal();
        }

        // Re-validate open documents once after processing all changes
        if should_revalidate {
            self.revalidate_open_documents();
        }
    }

    /// Re-validate all open documents (e.g., after an included file changes).
    fn revalidate_open_documents(&mut self) {
        let paths: Vec<_> = self.vfs.read().paths().cloned().collect();

        // Collect contents first to avoid borrow issues
        let documents: Vec<_> = paths
            .into_iter()
            .filter_map(|path| {
                let content = self.vfs.read().get_content(&path)?;
                let uri_str = format!("file://{}", path.display());
                let uri = uri_str.parse::<Uri>().ok()?;
                Some((uri, content))
            })
            .collect();

        // Now publish diagnostics
        for (uri, content) in documents {
            tracing::debug!("Revalidating: {}", uri.as_str());
            self.publish_diagnostics(&uri, &content);
        }
    }

    /// Register file watchers with the client.
    fn register_file_watchers(&self) {
        // Create a registration request for file watching
        let watchers = vec![
            lsp_types::FileSystemWatcher {
                glob_pattern: lsp_types::GlobPattern::String("**/*.beancount".to_string()),
                kind: Some(lsp_types::WatchKind::all()),
            },
            lsp_types::FileSystemWatcher {
                glob_pattern: lsp_types::GlobPattern::String("**/*.bean".to_string()),
                kind: Some(lsp_types::WatchKind::all()),
            },
        ];

        let registration = lsp_types::Registration {
            id: "file-watcher".to_string(),
            method: "workspace/didChangeWatchedFiles".to_string(),
            register_options: Some(
                serde_json::to_value(lsp_types::DidChangeWatchedFilesRegistrationOptions {
                    watchers,
                })
                .unwrap_or_default(),
            ),
        };

        let params = lsp_types::RegistrationParams {
            registrations: vec![registration],
        };

        // Send the registration request
        let request = lsp_server::Request::new(
            lsp_server::RequestId::from("register-file-watchers".to_string()),
            "client/registerCapability".to_string(),
            params,
        );

        self.send(lsp_server::Message::Request(request));
        tracing::info!("Registered file watchers for *.beancount and *.bean files");
    }

    /// Parse document and publish diagnostics (parse errors + validation errors).
    ///
    /// When a full ledger is loaded (multi-file mode), validation considers all
    /// files in the ledger, providing accurate diagnostics for balance assertions
    /// that depend on transactions in other files.
    ///
    /// To handle unsaved edits in multiple open buffers (#685 / #760), this
    /// collects fresh parses from the VFS for every open document that is
    /// part of the ledger and hands them to `all_diagnostics` as overlays.
    /// The VFS caches parses per document and invalidates on update, so
    /// this is usually a cache hit (O(1) per open buffer) except immediately
    /// after an edit to that buffer.
    fn publish_diagnostics(&mut self, uri: &Uri, text: &str) {
        // Parse the current document.
        let result = parse(text);

        // Canonicalize the current URI's path so we can both skip it when
        // collecting "other" buffer overlays and look up its file_id in
        // the ledger source map.
        let current_canonical_path = uri_to_path(uri).and_then(|p| p.canonicalize().ok());

        // Collect fresh parses for every OTHER open buffer via the VFS.
        // Done before grabbing the ledger-state read lock so the VFS
        // write lock (needed by the cache-aware iterator) is released
        // before we start the file_id lookups.
        //
        // We skip:
        //   - the current file (its fresh parse is already in `result`)
        //   - any buffer whose fresh parse has errors (keeping the stale
        //     ledger directives is better than overlaying a partial parse)
        //
        // Each entry returns the canonicalized path + the cached Arc of
        // the parse result, which owns the directives we hand into
        // `all_diagnostics`. The Arc keeps them alive for the call.
        let other_buffer_parses: Vec<(PathBuf, Arc<ParseResult>)> = {
            let mut vfs = self.vfs.write();
            vfs.iter_with_parse()
                .filter_map(|(path, _text, parsed)| {
                    let canonical = path.canonicalize().ok()?;
                    if Some(&canonical) == current_canonical_path.as_ref() {
                        return None;
                    }
                    if !parsed.errors.is_empty() {
                        return None;
                    }
                    Some((canonical, parsed))
                })
                .collect()
        };

        // Get ledger state and the current file's file_id.
        let ledger_guard = self.ledger_state.read();
        let (ledger_state, current_file_id) = if ledger_guard.ledger().is_some() {
            // Find the file_id for this URI by matching against included files.
            // Canonicalized comparison handles path normalization (e.g.,
            // /a/b/../c vs /a/c, or symlinks).
            let file_id = current_canonical_path.as_ref().and_then(|canonical| {
                ledger_guard.ledger().and_then(|ledger| {
                    ledger.source_map.files().iter().find_map(|f| {
                        f.path
                            .canonicalize()
                            .ok()
                            .filter(|canonical_f| canonical_f == canonical)
                            .map(|_| f.id as u16)
                    })
                })
            });
            (Some(&*ledger_guard), file_id)
        } else {
            (None, None)
        };

        // Resolve each other buffer's file_id against the ledger source
        // map. Buffers that aren't part of the ledger get dropped (they
        // can't affect validation anyway).
        let other_buffer_overlays: Vec<(u16, &[Spanned<Directive>])> =
            if let Some(ls) = ledger_state {
                let ledger = ls.ledger().expect("ledger_state.ledger() checked above");
                other_buffer_parses
                    .iter()
                    .filter_map(|(canonical, parsed)| {
                        let fid = ledger.source_map.files().iter().find_map(|f| {
                            f.path
                                .canonicalize()
                                .ok()
                                .filter(|canonical_f| canonical_f == canonical)
                                .map(|_| f.id as u16)
                        })?;
                        Some((fid, parsed.directives.as_slice()))
                    })
                    .collect()
            } else {
                Vec::new()
            };

        // Convert parse errors and validation errors to LSP diagnostics
        let diagnostics = all_diagnostics(
            &result,
            text,
            ledger_state,
            current_file_id,
            current_canonical_path.as_deref(),
            &other_buffer_overlays,
            self.position_encoding,
        );
        drop(ledger_guard); // Release lock before sending

        tracing::debug!(
            "Publishing {} diagnostics for {} (file_id: {:?})",
            diagnostics.len(),
            uri.as_str(),
            current_file_id
        );

        // Cache and send
        self.diagnostics.insert(uri.clone(), diagnostics.clone());
        self.send_diagnostics(uri, diagnostics);
    }

    /// Send diagnostics to the client.
    fn send_diagnostics(&self, uri: &Uri, diagnostics: Vec<lsp_types::Diagnostic>) {
        let params = PublishDiagnosticsParams {
            uri: uri.clone(),
            diagnostics,
            version: None,
        };

        let notif = lsp_server::Notification::new(PublishDiagnostics::METHOD.to_string(), params);

        self.send(lsp_server::Message::Notification(notif));
    }

    /// Send a message to the client.
    fn send(&self, msg: lsp_server::Message) {
        if let Err(e) = self.sender.send(msg) {
            tracing::error!("Failed to send message: {}", e);
        }
    }
}

/// Run the main event loop.
///
/// Uses `crossbeam_channel::select!` to multiplex between incoming LSP
/// messages and results from background task threads, keeping the main
/// loop responsive while expensive requests run in parallel.
///
/// # Arguments
///
/// * `receiver` - Channel to receive LSP messages from the client
/// * `sender` - Channel to send LSP messages to the client
/// * `journal_file` - Optional path to the root journal file for multi-file support
///
/// # Returns
///
/// The exit code from the `exit` notification (after the loop breaks
/// cleanly), or `0` if the channel was closed before an `exit`
/// notification arrived. The caller is expected to drain any IO
/// threads (e.g., `lsp_server::Connection::stdio()`'s
/// `io_threads.join()`) AFTER this returns and BEFORE terminating the
/// process - otherwise the shutdown response queued in the writer
/// thread's channel never reaches the client, which is the bug behind
/// the `stdio_smoke` CI flake.
#[must_use]
pub fn run_main_loop(
    receiver: Receiver<lsp_server::Message>,
    sender: Sender<lsp_server::Message>,
    journal_file: Option<PathBuf>,
    position_encoding: crate::handlers::utils::PositionEncoding,
) -> i32 {
    // No-op exit_action: the actual process termination (if any) is
    // the caller's responsibility, performed AFTER io_threads.join()
    // has drained the writer. The returned code is the source of
    // truth.
    run_main_loop_with_exit_action(
        receiver,
        sender,
        journal_file,
        position_encoding,
        |_code| {},
    )
}

/// Same as [`run_main_loop`] but with a caller-supplied `exit_action`
/// invoked when the `exit` notification arrives.
///
/// Production calls [`run_main_loop`], which wires the action to a
/// no-op (process termination, if any, is the caller's responsibility
/// AFTER `io_threads.join()`). The in-process integration test harness
/// calls this entry point with a no-op so receipt of `exit` does NOT
/// terminate the cargo-test process. After the no-op returns, the
/// main loop continues running until the connection is closed; the
/// harness completes shutdown by dropping the client side of the
/// `Connection::memory()` pair, which closes the channel and makes
/// the inner `select!` return `Err`, breaking the loop cleanly.
///
/// # Example
///
/// ```ignore
/// use lsp_server::Connection;
/// use rustledger_lsp::{handlers::utils::PositionEncoding, run_main_loop_with_exit_action};
///
/// let (server, client) = Connection::memory();
/// std::thread::spawn(move || {
///     run_main_loop_with_exit_action(
///         server.receiver,
///         server.sender,
///         None,
///         PositionEncoding::Utf8,
///         |_code| {}, // test harness: don't terminate the process
///     );
/// });
/// // ... drive `client` with LSP messages ...
/// drop(client); // closes the channel; the server thread exits.
/// ```
#[must_use]
pub fn run_main_loop_with_exit_action<F>(
    receiver: Receiver<lsp_server::Message>,
    sender: Sender<lsp_server::Message>,
    journal_file: Option<PathBuf>,
    position_encoding: crate::handlers::utils::PositionEncoding,
    exit_action: F,
) -> i32
where
    F: FnOnce(i32) + Send + 'static,
{
    let mut state = MainLoopState::new(sender, journal_file).with_exit_action(exit_action);
    state.position_encoding = position_encoding;
    let task_receiver = state.task_receiver.clone();

    tracing::info!("Main loop started");

    let exit_code = loop {
        crossbeam_channel::select! {
            recv(receiver) -> msg => {
                let msg = match msg {
                    Ok(msg) => msg,
                    Err(_) => break 0, // Channel closed without an `exit` notification.
                };
                let event = match msg {
                    lsp_server::Message::Request(req) => Event::Message(Message::Request(req)),
                    lsp_server::Message::Notification(notif) => {
                        Event::Message(Message::Notification(notif))
                    }
                    lsp_server::Message::Response(resp) => Event::Message(Message::Response(resp)),
                };
                state.handle_event(event);
            }
            recv(task_receiver) -> task_result => {
                if let Ok(result) = task_result {
                    state.handle_event(Event::Task(result));
                }
            }
        }
        // The `exit` notification handler signals via `pending_exit_code`
        // instead of calling `process::exit` directly. Break here so
        // the caller can drain the writer thread before terminating
        // the process; otherwise the queued shutdown response can be
        // lost on slow IO. See the field's rustdoc and the
        // `stdio_smoke` flake discussion.
        if let Some(code) = state.pending_exit_code {
            break code;
        }
    };

    tracing::info!("Main loop ended (exit code {exit_code})");
    exit_code
}

#[cfg(test)]
mod tests {
    use super::*;

    /// Pin the structural error-code mapping. Round-20 introduced
    /// `DispatchError` to replace the prior `msg.starts_with("...")`
    /// routing in `handle_request`; this test guards against silent
    /// regressions where a future refactor swaps a variant's mapped
    /// code (e.g. routing `DuplicateInitialize` to `InternalError`,
    /// which would mask a client-side protocol violation as a server
    /// fault).
    #[test]
    fn dispatch_error_codes() {
        // `lsp_server::ErrorCode` doesn't implement PartialEq, so
        // compare via the wire integer (which is what we serialize).
        assert_eq!(
            DispatchError::MethodNotFound("foo/bar".into()).error_code() as i32,
            lsp_server::ErrorCode::MethodNotFound as i32,
        );
        assert_eq!(
            DispatchError::DuplicateInitialize.error_code() as i32,
            lsp_server::ErrorCode::InvalidRequest as i32,
        );
        assert_eq!(
            DispatchError::Handler("boom".into()).error_code() as i32,
            lsp_server::ErrorCode::InternalError as i32,
        );
    }

    /// `Display` produces stable, distinguishable messages - clients
    /// (and humans tailing logs) shouldn't see the same string for
    /// two different failure modes.
    #[test]
    fn dispatch_error_display() {
        let unhandled = DispatchError::MethodNotFound("foo/bar".into()).to_string();
        assert!(
            unhandled.contains("foo/bar"),
            "MethodNotFound should include the method name: {unhandled}",
        );

        let dup_init = DispatchError::DuplicateInitialize.to_string();
        assert!(
            dup_init.contains("exactly once"),
            "DuplicateInitialize message should cite the spec invariant: {dup_init}",
        );

        let handler = DispatchError::Handler("custom failure".into()).to_string();
        assert_eq!(handler, "custom failure");
    }
}
