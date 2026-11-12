//! Main event loop for the LSP server.
//!
//! Follows rust-analyzer's architecture:
//! - Notifications handled synchronously (critical for correctness)
//! - Requests dispatched to threadpool with immutable snapshots
//! - Revision counter enables cancellation of stale requests

use crate::AbsPathBuf;
use crate::diagnostics_schedule::{DIAGNOSTICS_DEBOUNCE, DiagnosticsSchedule};
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
use rustledger_parser::{ParseResult, Spanned, bom, parse};
use std::collections::HashMap;
use std::path::PathBuf;
use std::sync::Arc;
use std::time::Instant;

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
    /// Set when the world changed (revision bumped) between dispatch and
    /// completion: the result is stale and is reported to the client as
    /// `ContentModified` instead of being silently dropped (which would leave a
    /// strict client waiting forever for a response that never comes).
    pub content_modified: bool,
}

/// LSP `ContentModified` error code (the document changed while the request was
/// in flight). Defined in LSP but not exposed by `lsp_server::ErrorCode`.
const CONTENT_MODIFIED: i32 = -32801;

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
    /// Cached diagnostics per file, keyed by PATH, not by `Uri`.
    ///
    /// A `Uri` is a string, and one file has many spellings of it: `%2F` vs
    /// `/`, a `.` segment, `C:` vs `c:`. Two spellings hash differently, so a
    /// map keyed by `Uri` can hold the same file twice, and the `didClose`
    /// that arrives in the client's spelling then fails to evict an entry
    /// stored in ours — diagnostics for a closed file stay on screen with no
    /// buffer left to clear them. Paths have no such freedom: `uri_to_path`
    /// resolves the encoding and dot segments, so every spelling of one file
    /// converges on one key.
    ///
    /// The URI exists at the protocol boundary and nowhere else, which is the
    /// same reason the VFS is path-keyed. Deliberately NOT canonicalized:
    /// `canonicalize` hits the filesystem, fails outright for a file that does
    /// not exist yet, and resolves symlinks the user may have opened on
    /// purpose. rust-analyzer's `AbsPathBuf` avoids it for those reasons.
    pub diagnostics: HashMap<AbsPathBuf, Vec<lsp_types::Diagnostic>>,
    /// Paths of *unopened* ledger files (reachable via `include`) that we last
    /// published non-empty diagnostics for. Tracked so that, when their errors
    /// are fixed, we send an explicit empty diagnostic set to clear them — the
    /// LSP spec has no implicit "clear", and these files have no open buffer of
    /// their own to drive a clear via `on_did_close`. Path-keyed for the reason
    /// above, and additionally because this set is compared against the VFS's
    /// open paths: keying it by `Uri` meant round-tripping every open path
    /// through the URI encoder just to compare it.
    pub cross_file_diag_paths: std::collections::HashSet<AbsPathBuf>,
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
    /// What each candidate root was found to reach, once probed.
    ///
    /// Probing costs a full ledger load and the search runs on every `didOpen`
    /// until a root is adopted, so a stray `main.beancount` over an unrelated
    /// ledger would otherwise be re-loaded once per file the user opens.
    ///
    /// The value is what makes this correct rather than merely fast. A flat
    /// "rejected" set was wrong: whether a root qualifies depends on the file
    /// being opened, so a root rejected while looking for one file could never
    /// be adopted for another, including for ITSELF. Caching the file set
    /// instead answers per target from one load. `None` records the answers
    /// that are target-independent: it would not load, or its includes
    /// resolved to nothing.
    ///
    /// Cleared whenever a watched `.beancount` file changes, since an edit is
    /// what could make a root start including a file it did not before.
    probed_roots: HashMap<PathBuf, Option<std::collections::HashSet<PathBuf>>>,
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
    /// Documents edited since their last diagnostics pass, and when that pass
    /// falls due (#2940). `didChange` schedules here instead of validating, so
    /// a burst of edits costs one pass instead of one per change; the main
    /// loop runs due passes from a timer arm. See [`DiagnosticsSchedule`].
    diagnostics_schedule: DiagnosticsSchedule,
    /// Source of "now" for the schedule. `Instant::now` in production; tests
    /// substitute a hand-advanced clock so debouncing is checked without
    /// sleeping.
    clock: Box<dyn Fn() -> Instant + Send>,
    /// Number of diagnostics passes run so far. Only read by tests, which
    /// assert that a burst of edits costs exactly one.
    #[cfg_attr(not(test), allow(dead_code))]
    diagnostics_passes: u64,
}

/// The `file_id` of the ledger file at `canonical`, if it is one. Compared
/// canonicalized on both sides, which handles path normalization (e.g.,
/// `/a/b/../c` vs `/a/c`, or symlinks).
fn ledger_file_id(ledger: &rustledger_loader::Ledger, canonical: &std::path::Path) -> Option<u16> {
    ledger.source_map.files().iter().find_map(|f| {
        f.path
            .canonicalize()
            .ok()
            .filter(|canonical_f| canonical_f == canonical)
            .map(|_| f.id as u16)
    })
}

/// The open buffers' part of the clean view (see
/// `MainLoopState::publish_diagnostics`): each open ledger buffer's
/// clean-view parse ([`crate::vfs::Document::clean_view_parse`]), keyed by its
/// `file_id`. A buffer that has not parsed cleanly since it was opened has
/// none and is left out, so its file is validated as the ledger loaded it.
/// Buffers that are not part of the ledger cannot affect its validation and
/// are dropped.
fn clean_buffer_overlays<'a>(
    ledger: &rustledger_loader::Ledger,
    parses: &'a [(PathBuf, Arc<ParseResult>)],
) -> Vec<(u16, &'a ParseResult)> {
    parses
        .iter()
        .filter_map(|(canonical, parsed)| Some((ledger_file_id(ledger, canonical)?, &**parsed)))
        .collect()
}

/// The directives of a view, for the single-file path, which takes them
/// without plugins.
fn view_directives<'a>(view: &[(u16, &'a ParseResult)]) -> Vec<(u16, &'a [Spanned<Directive>])> {
    view.iter()
        .map(|(fid, parsed)| (*fid, parsed.directives.as_slice()))
        .collect()
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
            cross_file_diag_paths: std::collections::HashSet::new(),
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
            probed_roots: HashMap::new(),
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
            diagnostics_schedule: DiagnosticsSchedule::new(DIAGNOSTICS_DEBOUNCE),
            clock: Box::new(Instant::now),
            diagnostics_passes: 0,
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
            let loaded = self.ledger_state.write().load(path);
            match loaded {
                Ok(_) => self.forget_clean_parses_of_loaded_buffers(),
                Err(e) => tracing::error!("Failed to reload journal file: {e}"),
            }
        }
    }

    /// After a load of the ledger: every open buffer whose current text is
    /// the text that load read for its file is now as loaded (it was saved),
    /// so it gives up its last clean parse
    /// ([`crate::vfs::Document::forget_last_clean_parse`]). Until it next
    /// parses cleanly, its file is then validated as `rledger check`
    /// validates the saved text, parse error and all, and not as the last
    /// clean text a diagnostics pass saw. A buffer whose text differs from
    /// what was loaded (unsaved edits on top of the save) keeps it.
    ///
    /// There is no `didSave` handler: the watched-file change that a save
    /// raises, and the reload it triggers, is the save signal. Matching the
    /// text, not the event, also covers a root adopted from a file already
    /// saved broken, and an external write that happens to equal the buffer.
    fn forget_clean_parses_of_loaded_buffers(&mut self) {
        // The loaded text of every file, keyed by canonical path, collected
        // under the ledger-state read lock and released before the VFS write
        // lock is taken (the order `open_buffer_parses` keeps).
        let loaded: HashMap<PathBuf, rustledger_loader::SourceText> = {
            let guard = self.ledger_state.read();
            let Some(ledger) = guard.ledger() else {
                return;
            };
            ledger
                .source_map
                .files()
                .iter()
                .filter_map(|f| Some((f.path.canonicalize().ok()?, f.source.clone())))
                .collect()
        };
        let paths: Vec<PathBuf> = self.vfs.read().paths().cloned().collect();
        let mut vfs = self.vfs.write();
        for path in paths {
            let Some(source) = path.canonicalize().ok().and_then(|c| loaded.get(&c)) else {
                continue;
            };
            // The loader keeps a file's leading BOM and an editor sends the
            // buffer without it; only the parser strips it. Compare the two
            // texts as the parser reads them.
            if let Some(doc) = vfs.get_mut(&path)
                && bom::strip_leading(&doc.text()).0 == bom::strip_leading(source.as_str()).0
            {
                doc.forget_last_clean_parse();
            }
        }
    }

    /// Get document text and cached parse result for a URI.
    /// Uses cached parse result if available, avoiding re-parsing.
    fn get_document_data(&self, uri: &Uri) -> (String, Arc<ParseResult>) {
        if let Ok(path) = uri_to_path(uri)
            && let Some((text, parse_result)) = self.vfs.write().get_document_data(path.as_path())
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
                let response = if task_result.content_modified {
                    lsp_server::Response::new_err(
                        task_result.request_id,
                        CONTENT_MODIFIED,
                        "document changed while the request was in flight; \
                         re-request for up-to-date results"
                            .to_string(),
                    )
                } else {
                    match task_result.result {
                        Ok(value) => lsp_server::Response::new_ok(task_result.request_id, value),
                        Err(msg) => lsp_server::Response::new_err(
                            task_result.request_id,
                            lsp_server::ErrorCode::InternalError as i32,
                            msg,
                        ),
                    }
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

            // If the world changed since dispatch, the result is stale.
            // Report ContentModified rather than dropping it: a strict client
            // tracking pending requests would otherwise wait forever for a
            // response that never arrives. It re-requests on the next edit.
            // Skipped for unconditional dispatch (stateless handlers).
            if let Some(rev) = dispatch_revision
                && revision_arc.load(std::sync::atomic::Ordering::SeqCst) != rev
            {
                tracing::debug!(
                    "Result for request {:?} is stale (revision changed); replying ContentModified",
                    request_id
                );
                // `result` is unused on the `content_modified` path (the
                // consumer emits a ContentModified error), but use `Err` so the
                // value never reads as a success if future code forgets the flag.
                let _ = task_sender.send(TaskResult {
                    request_id,
                    result: Err("stale result (content modified)".to_string()),
                    content_modified: true,
                });
                return;
            }

            // Ignore send errors - the main loop may have shut down
            let _ = task_sender.send(TaskResult {
                request_id,
                result,
                content_modified: false,
            });
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
                // Drop the debounced passes still owed: nothing should be
                // published after `shutdown`. `handle_notification` ignores
                // document and watched-file notifications from here on, so
                // none can be scheduled or published again either.
                self.diagnostics_schedule.clear();
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

        // Other ledger files so "find references" spans every `include`d file,
        // not just the open buffer. Collected under the locks (live content for
        // open buffers); the handler then parses lock-free.
        let current_canonical = uri_to_path(uri)
            .ok()
            .and_then(|p| p.canonical_for_loader_lookup());
        let other_files = self.other_ledger_files(current_canonical.as_deref());

        let response = handle_references(
            &params,
            &text,
            &parse_result,
            &other_files,
            uri,
            self.position_encoding,
        );

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

        // Collect all open documents with cached parse results.
        let mut documents: Vec<(Uri, String, Arc<ParseResult>)> = {
            let mut vfs = self.vfs.write();
            vfs.iter_with_parse()
                .filter_map(|(path, content, parse_result)| {
                    // SKIP, never a sentinel. `file:///` as a fallback pointed
                    // every unconvertible buffer at the filesystem root, so a
                    // workspace-symbol hit navigated nowhere — and two such
                    // buffers collapsed onto one key, attributing one file's
                    // symbols to the other. The sibling sites already skip.
                    let uri = crate::path_to_uri(path);
                    match uri {
                        Ok(uri) => Some((uri, content, parse_result)),
                        Err(e) => {
                            tracing::warn!("no file URI for {}: {e}; skipping", path.display());
                            None
                        }
                    }
                })
                .collect()
        };

        // Add ledger files reachable via `include` that aren't open, so
        // workspace symbol search spans the whole project — not just the
        // buffers the user happens to have open. Open buffers are listed first
        // (and the handler dedups by name), so their live edits take precedence
        // over the ledger snapshot.
        let open_canonical: std::collections::HashSet<PathBuf> = self
            .vfs
            .read()
            .paths()
            .filter_map(|p| p.canonicalize().ok())
            .collect();
        // Collect the unopened ledger files' (uri, source) UNDER the lock, then
        // drop the guard before parsing — re-parsing a large ledger while
        // holding the state read-lock would block journal reloads.
        let unopened: Vec<(Uri, String)> = {
            let ledger_guard = self.ledger_state.read();
            ledger_guard.ledger().map_or_else(Vec::new, |ledger| {
                ledger
                    .source_map
                    .files()
                    .iter()
                    .filter(|f| {
                        f.path
                            .canonicalize()
                            .ok()
                            .is_none_or(|c| !open_canonical.contains(&c))
                    })
                    .filter_map(|f| match crate::path_to_uri(&f.path) {
                        Ok(uri) => Some((uri, f.source.to_string())),
                        Err(e) => {
                            tracing::warn!(
                                "workspace/symbol: no file URI for {}: {e}; skipping",
                                f.path.display()
                            );
                            None
                        }
                    })
                    .collect()
            })
        };
        for (uri, source) in unopened {
            let parsed = Arc::new(parse(&source));
            documents.push((uri, source, parsed));
        }

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

        // Gather the other ledger files (everything except the current buffer)
        // so the rename spans every `include`d file — otherwise references in
        // other files are left dangling. Collected under the locks here (with
        // each file's live buffer content when open) so the handler parses with
        // no locks held.
        let current_canonical = uri_to_path(uri)
            .ok()
            .and_then(|p| p.canonical_for_loader_lookup());
        let other_files = self.other_ledger_files(current_canonical.as_deref());

        let response = handle_rename(
            &params,
            &text,
            &parse_result,
            &other_files,
            self.position_encoding,
        );

        serde_json::to_value(response).map_err(|e| e.to_string())
    }

    /// Collect the ledger's files reachable via `include`, EXCLUDING the file at
    /// `current_canonical`, as `(uri, source)`. The source is the open buffer's
    /// live content when the file is open (so edit ranges match the client),
    /// else the loader's on-disk source. Locks are released before returning, so
    /// callers can parse without holding them.
    fn other_ledger_files(
        &self,
        current_canonical: Option<&std::path::Path>,
    ) -> Vec<(Uri, String)> {
        // Live content of every open buffer, keyed by canonical path.
        let open: std::collections::HashMap<PathBuf, String> = {
            let vfs = self.vfs.read();
            vfs.paths()
                .filter_map(|p| Some((p.canonicalize().ok()?, vfs.get_content(p)?)))
                .collect()
        };

        let ledger_guard = self.ledger_state.read();
        let mut out = Vec::new();
        if let Some(ledger) = ledger_guard.ledger() {
            for f in ledger.source_map.files() {
                let canon = f.path.canonicalize().ok();
                if canon.as_deref() == current_canonical {
                    continue;
                }
                let uri = match crate::path_to_uri(&f.path) {
                    Ok(uri) => uri,
                    Err(e) => {
                        tracing::warn!(
                            "rename: no file URI for {}: {e}; skipping",
                            f.path.display()
                        );
                        continue;
                    }
                };
                // Prefer the open buffer's live content over the on-disk source
                // so cross-file edit ranges line up with the client's buffer.
                let source = canon
                    .as_ref()
                    .and_then(|c| open.get(c).cloned())
                    .unwrap_or_else(|| f.source.to_string());
                out.push((uri, source));
            }
        }
        out
    }

    /// Handle the textDocument/formatting request.
    /// Run `f` with the grouping style that formatting `uri` should use.
    ///
    /// The style borrows the loaded ledger's `DisplayContext`, so it cannot
    /// outlive the read guard — hence the closure rather than a return value.
    /// Stated once here because all four formatting entry points (document,
    /// range, and both `executeCommand` paths) need the same resolution, and
    /// a per-site copy is how they would drift.
    ///
    /// A URI that does not resolve to a path yields the no-grouping default,
    /// as does a buffer outside the loaded ledger — see
    /// [`LedgerState::grouping_style_for`](crate::ledger_state::LedgerState::grouping_style_for).
    fn with_grouping_style<T>(
        &self,
        uri: &Uri,
        f: impl FnOnce(rustledger_parser::format::GroupingStyle<'_>) -> T,
    ) -> T {
        let ledger_guard = self.ledger_state.read();
        match uri_to_path(uri) {
            Ok(path) => f(ledger_guard.grouping_style_for(path.as_path())),
            Err(_) => f(rustledger_parser::format::GroupingStyle::default()),
        }
    }

    fn handle_formatting_request(
        &self,
        req: lsp_server::Request,
    ) -> Result<serde_json::Value, String> {
        let params: DocumentFormattingParams =
            serde_json::from_value(req.params).map_err(|e| e.to_string())?;

        let uri = &params.text_document.uri;
        let (text, parse_result) = self.get_document_data(uri);

        let response = self.with_grouping_style(uri, |style| {
            handle_formatting(&params, &text, &parse_result, self.position_encoding, style)
        });

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

        let response = self.with_grouping_style(uri, |style| {
            handle_range_formatting(&params, &text, &parse_result, self.position_encoding, style)
        });

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
        // The tooltip prefers the loaded whole-ledger pipeline output
        // (booked + pad-expanded) over the raw single-file parse.
        let ledger_guard = self.ledger_state.read();
        let resolved = handle_inlay_hint_resolve(hint, &parse_result, ledger_guard.ledger());

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
        let text = if let Ok(path) = uri_to_path(uri) {
            self.vfs
                .read()
                .get_content(path.as_path())
                .unwrap_or_default()
        } else {
            String::new()
        };

        let response = handle_on_type_formatting(&params, &text, self.position_encoding);

        serde_json::to_value(response).map_err(|e| e.to_string())
    }

    /// Handle the textDocument/codeLens request.
    fn handle_code_lens_request(
        &mut self,
        req: lsp_server::Request,
    ) -> Result<serde_json::Value, String> {
        let params: CodeLensParams =
            serde_json::from_value(req.params).map_err(|e| e.to_string())?;

        let uri = &params.text_document.uri;
        // The lens reads the diagnostics cache below. With a debounced pass
        // still pending (#2940) that cache describes text the user has since
        // edited, so settle the pass first rather than serve its verdict.
        self.flush_pending_diagnostics(uri);
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
        let cached_path = uri_to_path(uri).ok();
        let cached_diagnostics = cached_path
            .as_ref()
            .and_then(|p| self.diagnostics.get(p))
            .map(Vec::as_slice);

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
        let text = if let Ok(path) = uri_to_path(uri) {
            self.vfs
                .read()
                .get_content(path.as_path())
                .unwrap_or_default()
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
            let result = self.with_grouping_style(&uri, |style| {
                handle_execute_command(
                    &params,
                    &text,
                    &parse_result,
                    &uri,
                    self.position_encoding,
                    style,
                )
            });
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

        // One converter for both platforms. The `cfg` split here existed
        // because a Windows drive letter needs a third slash — the same bug the
        // other seven call sites still had, patched at this one.
        let uri: Uri = crate::path_to_uri(&path)
            .map_err(|e| format!("no file URI for {}: {e}", path.display()))?;

        let (text, parse_result) = self.get_document_data(&uri);
        let result = self.with_grouping_style(&uri, |style| {
            handle_execute_command(
                &params,
                &text,
                &parse_result,
                &uri,
                self.position_encoding,
                style,
            )
        });
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
        // After `shutdown`, the client may send only `exit` (LSP 3.17
        // §Lifecycle), and the server should not act on anything else. A
        // document or watched-file notification would otherwise run (or
        // schedule) a diagnostics pass and publish after shutdown.
        if self.shutdown_requested && notif.method != "exit" {
            tracing::debug!("Ignoring {} after shutdown", notif.method);
            return;
        }
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
        if let Ok(path) = uri_to_path(&uri) {
            // Hand this file's diagnostics over from the cross-file publisher
            // to the buffer BEFORE the buffer publishes its own.
            //
            // While the file was an unopened include, its errors went out under
            // the URI WE build from the loader's canonical path. From now on
            // they go out under the URI the CLIENT sent. Those are two
            // spellings of one file whenever the ledger is reached through a
            // symlink or a differently-cased path, and the client keys its
            // diagnostic store by URI — so without an explicit clear it shows
            // both sets, the stale one for a file it can see is open.
            //
            // `publish_cross_file_diagnostics` cannot do it: it deliberately
            // leaves open files alone, so once this file is open it stops
            // touching the entry at all and the old set is stranded.
            self.release_cross_file_diagnostics(&path);

            self.vfs
                .write()
                .open(path.into_path_buf(), text.clone(), version);
        }

        // A file that includes other files IS a root journal, whatever it is
        // called (#2285). Discovery only recognizes the names in
        // `COMMON_ROOT_NAMES`, so a ledger rooted at `m1.beancount` fell
        // through to single-file mode, where nothing follows an `include` and
        // every account opened in an included file read as never opened. The
        // editor then reported `E1001` on a file `rledger check` calls clean,
        // which is the worst shape of wrong: the tool contradicts itself, and
        // the surface the user is looking at is the one that is wrong.
        //
        // Only when no journal is configured or discovered, so an explicit
        // `rustledger.journalFile` still wins. Deliberately `didOpen` only: the
        // same check on every `didChange` would reload the whole ledger while
        // an include path is still half-typed.
        // BEFORE the adoption below, not after. Adoption loads the whole
        // ledger, which is much slower than the VFS write above, and a
        // background request completing inside that window would compare an
        // unchanged revision and be delivered as fresh while the world it was
        // computed against had already been replaced. Invalidating first makes
        // that window unreachable.
        self.bump_revision();

        let adopted = self.adopt_as_journal_if_it_has_includes(&uri);

        if adopted {
            // Adoption changes the ledger EVERY open document is validated
            // against, not just this one. A user who opened a transactions
            // file first saw its accounts reported unopened, and without this
            // those diagnostics sat there uncorrected until the file was
            // touched: the ledger knew better and the editor still said
            // otherwise. Covers this document too, since it is in the VFS by
            // now, so there is no separate publish for it.
            self.revalidate_open_documents();
        } else {
            // Compute and publish diagnostics
            self.publish_diagnostics(&uri, &text);
        }
    }

    /// Adopt a just-opened file as the root journal when it declares includes
    /// and we have no journal yet.
    ///
    /// Loading is what makes an `open` in an included file visible to
    /// validation, so this is the difference between a correct diagnostic and
    /// a false one.
    ///
    /// Adoption is STICKY -- `journal_file.is_some()` is what stops a second
    /// one -- so it only happens when the includes actually resolved, measured
    /// by the loader reaching more than the root file itself. An unresolved
    /// include is not an `Err`: the loader returns `Ok` with the failure
    /// recorded in `ledger.errors`, so a file whose include is missing or
    /// still half-typed would otherwise be adopted on the strength of an
    /// include that led nowhere, and would then lock the session out of the
    /// real root for good.
    /// Returns whether a root was adopted, since that invalidates the
    /// diagnostics of every already-open document, not just this one.
    fn adopt_as_journal_if_it_has_includes(&mut self, uri: &Uri) -> bool {
        if self.journal_file.is_some() {
            return false;
        }
        let Ok(path) = uri_to_path(uri) else {
            return false;
        };
        let path = path.into_path_buf();

        // Two ways to reach a root, in order of confidence.
        //
        // 1. The open file declares includes, so it IS a root, whatever it is
        //    called. This is the reported case (#2285).
        // 2. Otherwise look upward for a conventionally named root that turns
        //    out to include this file. A user editing `ledger/2025-01.beancount`
        //    hits the same wrong `E1001` as the reporter did, and that file
        //    declares no includes of its own, so (1) cannot help it.
        // 3. Failing that, any nearby file that declares an `include` at all.
        //    Discovery by name cannot see a root called `m1.beancount`, which
        //    is the reporter's own root, so without this the sub-files of any
        //    unconventionally named ledger keep reporting accounts as never
        //    opened.
        //
        // Ordered by confidence and by cost, and every candidate still has to
        // prove it reaches this file, so a wider net does not mean a wronger
        // answer.
        //
        // By SOURCE rather than by distance, which matters when more than one
        // root reaches the file. A master ledger including self-contained
        // sub-ledgers is a legitimate layout (#1546), and there the master is
        // the better answer even though the sub-ledger's own root is nearer:
        // the master gives complete cross-file validation, while the inner one
        // reports accounts the master opens as never opened. So this
        // deliberately does not extend `discover_journal_upward`'s
        // "nearest wins" across sources; nearest and most-complete point in
        // opposite directions here.
        let (_text, parsed) = self.get_document_data(uri);
        let mut candidates: Vec<PathBuf> = Vec::new();
        if !parsed.includes.is_empty() {
            candidates.push(path.clone());
        }
        if let Some(dir) = path.parent()
            && let Some(found) = rustledger_loader::discover_journal_upward(dir)
            && !candidates.contains(&found)
        {
            candidates.push(found);
        }
        let by_include = rustledger_loader::discover_include_roots_upward(&path);
        if by_include.len() == rustledger_loader::MAX_CANDIDATES {
            // Saying so, because the alternative is a wrong diagnostic that
            // looks ordinary: if the real root was the one dropped, this file
            // is validated alone and reports its accounts as never opened.
            tracing::warn!(
                "root search for {} hit the {}-candidate cap; if its root is missing, \
                 set `rustledger.journalFile`",
                path.display(),
                rustledger_loader::MAX_CANDIDATES
            );
        }
        for found in by_include {
            if !candidates.contains(&found) {
                candidates.push(found);
            }
        }

        // Canonical on both sides. `LedgerState::load` canonicalizes every
        // path it records, so the target has to be canonicalized too or a uri
        // carrying `..` or a symlink would miss a set that does contain it.
        let canonical_target = path.canonicalize().unwrap_or_else(|_| path.clone());

        for root in candidates {
            let reach = if let Some(cached) = self.probed_roots.get(&root) {
                cached.clone()
            } else {
                // Load into a SCRATCH state, never straight into the shared
                // one. A candidate that turns out not to qualify would
                // otherwise leave the server holding a ledger it just decided
                // not to use, with `journal_file` still None to say so: two
                // sources of truth disagreeing about which ledger is live.
                let mut probe = crate::ledger_state::LedgerState::new();
                // `files.len() > 1` because adoption is STICKY:
                // `journal_file.is_some()` is what stops a second one. An
                // unresolved include is not an `Err` -- the loader returns Ok
                // with the failure recorded in `ledger.errors` -- so a file
                // whose include is missing or still half-typed would otherwise
                // be adopted on the strength of an include that led nowhere.
                let reach = match probe.load(&root) {
                    Ok(files) if files.len() > 1 => Some(files),
                    Ok(_) => {
                        tracing::debug!(
                            "Not adopting {}: its includes resolved to nothing",
                            root.display()
                        );
                        None
                    }
                    Err(e) => {
                        tracing::warn!("Not adopting {} as a root journal: {e}", root.display());
                        None
                    }
                };
                self.probed_roots.insert(root.clone(), reach.clone());
                // Already loaded, so commit this one rather than loading again.
                if reach
                    .as_ref()
                    .is_some_and(|files| files.contains(&canonical_target))
                {
                    tracing::info!(
                        "Adopted {} as the root journal; none was configured",
                        root.display()
                    );
                    *self.ledger_state.write() = probe;
                    self.journal_file = Some(root);
                    self.forget_clean_parses_of_loaded_buffers();
                    return true;
                }
                continue;
            };

            // Cache hit. It reaches this file, so load it for real: the probe
            // that produced the cached answer was dropped with its state.
            if reach.is_some_and(|files| files.contains(&canonical_target)) {
                let mut state = crate::ledger_state::LedgerState::new();
                if state.load(&root).is_ok() {
                    tracing::info!(
                        "Adopted {} as the root journal (cached reach); none was configured",
                        root.display()
                    );
                    *self.ledger_state.write() = state;
                    self.journal_file = Some(root);
                    self.forget_clean_parses_of_loaded_buffers();
                    return true;
                }
                // It loaded a moment ago and does not now. Treat the cache as
                // stale rather than trusting it.
                self.probed_roots.remove(&root);
            }
        }
        false
    }

    /// Handle textDocument/didChange notification.
    fn on_did_change(&mut self, params: lsp_types::DidChangeTextDocumentParams) {
        let uri = params.text_document.uri;
        let version = params.text_document.version;

        // For full sync, take the last change (which is the full content)
        if let Some(change) = params.content_changes.into_iter().last() {
            let text = change.text;

            tracing::debug!("Document changed: {}", uri.as_str());

            // Apply the edit and bump the revision NOW, so every request from
            // here on (hover, completion, definition, ...) sees this text.
            let path = uri_to_path(&uri).ok();
            let in_vfs = path.as_ref().is_some_and(|path| {
                let mut vfs = self.vfs.write();
                let open = vfs.get(path.as_path()).is_some();
                vfs.update(path.as_path(), text.clone(), version);
                open
            });
            self.bump_revision();

            // Diagnostics, on the other hand, wait for the edits to pause
            // (#2940): a pass validates the whole ledger, and during a burst
            // every pass but the last is thrown away. The pass reads the text
            // from the VFS when it runs, so it can only ever describe the
            // latest version, never this intermediate one.
            //
            // A document that is not in the VFS leaves a deferred pass nothing
            // to read back, so it keeps the immediate publish from the text in
            // hand. That covers a URI with no file path, and a `didChange` with
            // no `didOpen` before it: a client protocol violation, but one the
            // server answered with diagnostics before #2940 and still does.
            match path.filter(|_| in_vfs) {
                Some(path) => {
                    let now = (self.clock)();
                    self.diagnostics_schedule.schedule(path, uri, now);
                }
                None => self.publish_diagnostics(&uri, &text),
            }
        }
    }

    /// Clear the cross-file diagnostics for a file that is now open.
    ///
    /// Matched in the LOADER's spelling, because that is what
    /// `cross_file_diag_paths` holds and the path arriving here came from the
    /// client. The clear is sent to the URI built from the TRACKED path, not
    /// the client's, since that is the one the old set was published under and
    /// the only one that will evict it.
    fn release_cross_file_diagnostics(&mut self, opened: &AbsPathBuf) {
        let Some(canonical) = opened.canonical_for_loader_lookup() else {
            return;
        };
        let tracked: Vec<AbsPathBuf> = self
            .cross_file_diag_paths
            .iter()
            .filter(|p| p.canonical_for_loader_lookup().as_deref() == Some(canonical.as_path()))
            .cloned()
            .collect();
        for path in tracked {
            self.cross_file_diag_paths.remove(&path);
            self.diagnostics.remove(&path);
            self.send_diagnostics(&path, vec![]);
        }
    }

    /// Handle textDocument/didClose notification.
    fn on_did_close(&mut self, params: lsp_types::DidCloseTextDocumentParams) {
        let uri = params.text_document.uri;

        tracing::info!("Document closed: {}", uri.as_str());

        // Remove from VFS and drop the cached diagnostics under the same key
        // the VFS uses. The clear still goes out on the URI the client sent,
        // which is what it will match against its own store.
        let mut in_ledger = false;
        if let Ok(path) = uri_to_path(&uri) {
            // A pass still pending for this buffer would re-publish what the
            // clear below removes, for a file the client no longer has open.
            self.diagnostics_schedule.cancel(&path);
            self.vfs.write().close(path.as_path());
            self.diagnostics.remove(&path);
            self.cross_file_diag_paths.remove(&path);
            in_ledger = self.ledger_state.read().contains_file(path.as_path());
        }
        self.send_diagnostics_to_uri(&uri, vec![]);

        // The closed buffer's unsaved text leaves the clean view with it, so
        // every other ledger file is republished from the view without it:
        // each other open ledger buffer from its own view, which republishes
        // the unopened files (now including this one) as well; with no other
        // ledger buffer open, the unopened files alone.
        if in_ledger {
            let others = self.open_ledger_documents();
            if others.is_empty() {
                self.publish_unopened_diagnostics();
            } else {
                for (uri, text) in others {
                    self.publish_diagnostics(&uri, &text);
                }
            }
        }
    }

    /// The URI and current text of every open buffer that is a file of the
    /// loaded ledger.
    fn open_ledger_documents(&self) -> Vec<(Uri, String)> {
        let vfs = self.vfs.read();
        let ledger_state = self.ledger_state.read();
        vfs.iter()
            .filter(|(path, _)| ledger_state.contains_file(path))
            .filter_map(|(path, text)| {
                let uri = crate::path_to_uri(path)
                    .map_err(|e| {
                        tracing::warn!("no file URI for {}: {e}; skipping", path.display());
                    })
                    .ok()?;
                Some((uri, text))
            })
            .collect()
    }

    /// Handle workspace/didChangeWatchedFiles notification.
    fn on_did_change_watched_files(&mut self, params: lsp_types::DidChangeWatchedFilesParams) {
        tracing::info!("Watched files changed: {} files", params.changes.len());

        let mut should_reload_journal = false;
        let mut should_revalidate = false;

        for change in params.changes {
            tracing::debug!("File {:?}: {:?}", change.uri.as_str(), change.typ);

            // Check if the changed file is part of our journal
            if let Ok(path) = uri_to_path(&change.uri) {
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

        // A rejected root is rejected against the tree as it was. An edit is
        // exactly what could add the `include` that makes it this file's root
        // after all, so the memo does not outlive one.
        if should_revalidate {
            self.probed_roots.clear();
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
                let uri = crate::path_to_uri(&path)
                    .map_err(|e| {
                        tracing::warn!("no file URI for {}: {e}; skipping", path.display());
                    })
                    .ok()?;
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

    /// When the earliest debounced diagnostics pass falls due, if any. The
    /// main loop sleeps until then (or until a message arrives).
    fn next_diagnostics_deadline(&self) -> Option<Instant> {
        self.diagnostics_schedule.next_deadline()
    }

    /// Run every debounced diagnostics pass whose deadline has passed.
    ///
    /// Each pass reads the document's text from the VFS at the moment it
    /// runs, so what gets published always describes the current version: an
    /// intermediate version of a burst is never validated at all, let alone
    /// published after a later one.
    fn run_due_diagnostics(&mut self) {
        let now = (self.clock)();
        for (path, uri) in self.diagnostics_schedule.take_due(now) {
            self.run_diagnostics_pass(&path, &uri);
        }
    }

    /// Run the pending diagnostics pass for `uri` now, ahead of its deadline.
    ///
    /// For requests that READ the diagnostics cache: a pending pass means the
    /// cache describes text the user has since changed, so answering from it
    /// would serve a stale verdict. Does nothing when no pass is pending.
    fn flush_pending_diagnostics(&mut self, uri: &Uri) {
        let Ok(path) = uri_to_path(uri) else {
            return;
        };
        if let Some(pending_uri) = self.diagnostics_schedule.cancel(&path) {
            self.run_diagnostics_pass(&path, &pending_uri);
        }
    }

    /// One pass for an open document, from its current text in the VFS. A
    /// document closed since the pass was scheduled has nothing to publish
    /// (its close already sent the clear).
    fn run_diagnostics_pass(&mut self, path: &AbsPathBuf, uri: &Uri) {
        let content = self.vfs.read().get_content(path.as_path());
        if let Some(content) = content {
            self.publish_diagnostics(uri, &content);
        }
    }

    /// Parse document and publish diagnostics (parse errors + validation errors).
    ///
    /// When a full ledger is loaded (multi-file mode), validation considers all
    /// files in the ledger, providing accurate diagnostics for balance assertions
    /// that depend on transactions in other files.
    ///
    /// To handle unsaved edits in multiple open buffers (#685 / #760), this
    /// collects fresh parses from the VFS for every open document that is
    /// part of the ledger and hands them to the validation as overlays.
    /// The VFS caches parses per document and invalidates on update, so
    /// this is usually a cache hit (O(1) per open buffer) except immediately
    /// after an edit to that buffer.
    ///
    /// # Which text each file is validated against (#2949, #1813)
    ///
    /// Two views of the ledger. "The ledger as loaded" below is the stored
    /// [`LedgerState`](crate::ledger_state::LedgerState) load: it is read
    /// from disk at startup or root adoption and re-read on a watched-file
    /// change, not on every save.
    ///
    /// - The CLEAN view: the ledger as loaded, with each open buffer's
    ///   clean-view parse overlaid, directives AND plugin lines: its current
    ///   parse when that has no error, else the last text of it a diagnostics
    ///   pass saw parse cleanly ([`crate::vfs::Document::clean_view_parse`]).
    ///   A buffer no pass has seen parse cleanly since it was opened is not
    ///   overlaid, and its file is as loaded; so is a buffer whose current
    ///   text a load has since read (it was saved broken, see below). The
    ///   plugins run by file and then declaration, as `check` runs them for
    ///   those texts, with the files in the order of the last load.
    ///   Every file other than the one being published (the unopened
    ///   includes that are cross-published from here, and the other open
    ///   buffers' own passes) is validated against this view.
    /// - The OWN view of the published buffer: the clean view with this
    ///   buffer's current text in its place, parse error or not, and the
    ///   plugins that text declares. Its diagnostics are what `rledger check`
    ///   reports for the ledger with that text, so a syntax error does not
    ///   hide the other findings in it. One caveat: the set AND ORDER of the
    ///   files come from the last load, so an `include` line added, removed,
    ///   changed or moved in a buffer takes effect when the ledger is next
    ///   loaded, and until then the buffer's own diagnostics (and, through
    ///   the clean view, other files') can differ from `check`'s. The order
    ///   matters as plugins run file by file in it, and same-day entries of
    ///   two files tie-break by it.
    ///
    /// For a buffer that parses cleanly the two views are the same, so there
    /// is ONE validation, as before. Only a broken buffer costs a second one,
    /// for its own diagnostics.
    ///
    /// Why the clean view keeps a broken buffer's last clean parse, not its
    /// text: a buffer broken mid-edit loses whatever the error swallowed
    /// (typing one `"` makes a string of every line up to the next quote,
    /// `open`s and `plugin`s included). Validating other files against it
    /// would put E1001s on them on that keystroke and take them away on the
    /// next. Falling back to the ledger as loaded instead would undo the
    /// buffer's unsaved clean edits for the other files on that keystroke,
    /// which flips them just the same. The clean view does not depend on
    /// which buffer is being published, so every file gets its diagnostics on
    /// every pass and a revalidation publishes each file the same way however
    /// many buffers it publishes. A file SAVED broken is in the ledger as
    /// loaded with its parse error, so its includes are validated as `rledger
    /// check` validates them: the load that reads it (a watched-file reload,
    /// or root adoption) also drops the last clean parse of an open buffer
    /// holding that same text (`forget_clean_parses_of_loaded_buffers`), so
    /// the buffer counts as loaded until it next parses cleanly. A buffer
    /// edited past what was saved keeps its last clean parse. Closing a
    /// buffer drops its clean-view parse,
    /// and every other ledger file is republished from the view without it
    /// (see `on_did_close`).
    fn publish_diagnostics(&mut self, uri: &Uri, text: &str) {
        self.diagnostics_passes += 1;
        // Every caller passes the document's current text, so this pass
        // settles any debounced one still pending for the same file. Covers
        // `didOpen`, root adoption and watched-file revalidation, which all
        // publish at once and would otherwise be followed by a redundant pass.
        let path = uri_to_path(uri).ok();
        if let Some(path) = &path {
            self.diagnostics_schedule.cancel(path);
        }

        // Parse the current document, through the VFS when it holds this
        // text, which also records a clean parse as the buffer's clean-view
        // parse. `current_clean` is that parse: this buffer's part of the
        // clean view.
        let (result, current_clean): (Arc<ParseResult>, Option<Arc<ParseResult>>) = {
            let mut vfs = self.vfs.write();
            match path
                .as_ref()
                .and_then(|path| vfs.get_mut(path.as_path()))
                .filter(|doc| doc.text() == text)
            {
                Some(doc) => (doc.parse_result(), doc.clean_view_parse()),
                None => {
                    let parsed = Arc::new(parse(text));
                    let clean = parsed.errors.is_empty().then(|| Arc::clone(&parsed));
                    (parsed, clean)
                }
            }
        };
        let current_is_clean = result.errors.is_empty();

        // Canonicalize the current URI's path so we can both skip it when
        // collecting "other" buffer overlays and look up its file_id in
        // the ledger source map.
        let current_canonical_path = path.as_ref().and_then(|p| p.canonical_for_loader_lookup());

        // Clean-view parses for every OTHER open buffer, before the
        // ledger-state read lock is taken (see `open_buffer_parses`).
        let other_buffer_parses = self.open_buffer_parses(current_canonical_path.as_deref());

        // Get ledger state and the current file's file_id.
        let ledger_guard = self.ledger_state.read();
        let (ledger_state, current_file_id) = if let Some(ledger) = ledger_guard.ledger() {
            let file_id = current_canonical_path
                .as_deref()
                .and_then(|canonical| ledger_file_id(ledger, canonical));
            (Some(&*ledger_guard), file_id)
        } else {
            (None, None)
        };

        // The other open buffers' part of the clean view.
        let other_buffer_overlays: Vec<(u16, &ParseResult)> = ledger_state
            .and_then(crate::ledger_state::LedgerState::ledger)
            .map(|ledger| clean_buffer_overlays(ledger, &other_buffer_parses))
            .unwrap_or_default();

        // Is this a multi-file ledger? If so, the unopened files' diagnostics
        // (and, for a clean buffer, its own) come from a SINGLE whole-ledger
        // validation (`ledger_diagnostics_multi`), the #1799 fix. Otherwise
        // fall back to the single-file `all_diagnostics` path.
        let is_multi_file = ledger_state
            .and_then(|ls| ls.ledger())
            .is_some_and(|l| l.source_map.files().len() > 1);

        let (diagnostics, cross_file) = if is_multi_file {
            let ledger_state = ledger_state.expect("is_multi_file implies a loaded ledger");
            // The clean view: this buffer's clean-view parse, if it is a
            // ledger file and has one, plus the other buffers'.
            let mut clean_view: Vec<(u16, &ParseResult)> =
                Vec::with_capacity(1 + other_buffer_overlays.len());
            if let (Some(fid), Some(clean)) = (current_file_id, current_clean.as_deref()) {
                clean_view.push((fid, clean));
            }
            clean_view.extend_from_slice(&other_buffer_overlays);

            // This buffer is a target of the clean view's validation only
            // when its current text parses cleanly: then the clean view IS
            // its own view.
            let clean_file_id = current_file_id.filter(|_| current_is_clean);
            let (current_from_multi, cross) = self.multi_file_diagnostics(
                ledger_state,
                current_canonical_path.as_deref(),
                clean_file_id,
                &result,
                text,
                &clean_view,
            );
            let current = match current_file_id {
                // Clean: its own view IS the clean view, so its diagnostics
                // came from the one validation above.
                Some(_) if current_is_clean => current_from_multi,
                // Broken: a second validation, of its own view, in which its
                // current text replaces its clean-view parse.
                Some(fid) => {
                    let mut own_view = clean_view;
                    own_view.retain(|(f, _)| *f != fid);
                    own_view.push((fid, &*result));
                    let target = crate::handlers::diagnostics::FileDiagTarget {
                        file_id: fid,
                        source: text,
                        parse: &result,
                    };
                    crate::handlers::diagnostics::ledger_diagnostics_multi(
                        ledger_state,
                        &own_view,
                        &[target],
                        self.position_encoding,
                    )
                    .pop()
                    .unwrap_or_default()
                }
                // Not part of the ledger (e.g. a scratch file while a
                // multi-file ledger is loaded): it self-validates via the
                // single-file path, and the unopened files' diagnostics above
                // are still republished, not cleared.
                None => all_diagnostics(
                    &result,
                    text,
                    Some(ledger_state),
                    None,
                    current_canonical_path.as_deref(),
                    &view_directives(&other_buffer_overlays),
                    self.position_encoding,
                ),
            };
            (current, cross)
        } else {
            // Single-file (or no loaded ledger): validate just the current
            // file. There are no unopened files to publish.
            let diagnostics = all_diagnostics(
                &result,
                text,
                ledger_state,
                current_file_id,
                current_canonical_path.as_deref(),
                &view_directives(&other_buffer_overlays),
                self.position_encoding,
            );
            (diagnostics, Vec::new())
        };
        drop(ledger_guard); // Release lock before sending

        tracing::debug!(
            "Publishing {} diagnostics for {} (file_id: {:?})",
            diagnostics.len(),
            uri.as_str(),
            current_file_id
        );

        // Cache under the path, send to the URI the client gave us.
        if let Some(path) = path {
            self.diagnostics.insert(path, diagnostics.clone());
        }
        self.send_diagnostics_to_uri(uri, diagnostics);

        // Publish (or clear) diagnostics for unopened included files.
        self.publish_cross_file_diagnostics(cross_file);
    }

    /// Republish the unopened files of a multi-file ledger from the clean
    /// view (see [`Self::publish_diagnostics`]), with no buffer being
    /// published. For a `didClose` that leaves no other ledger buffer open:
    /// the closed buffer's unsaved text, if it was in the clean view, no
    /// longer is, and the file is now unopened itself.
    fn publish_unopened_diagnostics(&mut self) {
        let parses = self.open_buffer_parses(None);
        let ledger_guard = self.ledger_state.read();
        let Some(ledger) = ledger_guard.ledger() else {
            return;
        };
        if ledger.source_map.files().len() <= 1 {
            return;
        }
        let clean_view = clean_buffer_overlays(ledger, &parses);
        let empty = parse("");
        let (_, cross) =
            self.multi_file_diagnostics(&ledger_guard, None, None, &empty, "", &clean_view);
        drop(ledger_guard);
        self.publish_cross_file_diagnostics(cross);
    }

    /// The clean-view parse of every open buffer except `skip` (see
    /// [`crate::vfs::Document::clean_view_parse`]; a buffer with none is
    /// left out), keyed by canonical path, through the VFS's parse cache. Taken before the ledger-state read
    /// lock so the VFS write lock (needed by the cache-aware iterator) is
    /// released before the `file_id` lookups. The `Arc`s own the directives
    /// handed to validation as overlays.
    fn open_buffer_parses(
        &self,
        skip: Option<&std::path::Path>,
    ) -> Vec<(PathBuf, Arc<ParseResult>)> {
        let mut vfs = self.vfs.write();
        vfs.iter_clean_view_parses()
            .filter_map(|(path, parsed)| {
                let canonical = path.canonicalize().ok()?;
                if Some(canonical.as_path()) == skip {
                    return None;
                }
                Some((canonical, parsed))
            })
            .collect()
    }

    /// Compute the current file's diagnostics AND every unopened included
    /// file's diagnostics from a SINGLE whole-ledger validation (#1799).
    ///
    /// Returns `(current_file_diagnostics, cross_file)`, where `cross_file` is
    /// one `(path, diagnostics)` per unopened ledger file (diagnostics may be
    /// empty — the caller clears those it had previously reported). This
    /// replaces the old per-file `all_diagnostics` loop, which re-ran the whole
    /// ledger's book+validate once per file: that O(files) cost per keystroke
    /// starved the LSP main loop and made completions time out on large
    /// multi-file ledgers.
    ///
    /// Only unopened files are cross-published; open buffers self-publish via
    /// didOpen/didChange. `overlay` is the clean view (see
    /// [`Self::publish_diagnostics`]); `current_file_id` is `Some` only when
    /// the current buffer is part of it, and then its diagnostics come from
    /// the same validation.
    fn multi_file_diagnostics(
        &self,
        ledger_state: &crate::ledger_state::LedgerState,
        current_canonical: Option<&std::path::Path>,
        current_file_id: Option<u16>,
        current_parse: &ParseResult,
        current_source: &str,
        overlay: &[(u16, &ParseResult)],
    ) -> (
        Vec<lsp_types::Diagnostic>,
        Vec<(AbsPathBuf, Vec<lsp_types::Diagnostic>)>,
    ) {
        let Some(ledger) = ledger_state.ledger() else {
            return (Vec::new(), Vec::new());
        };

        // Canonical paths of all open buffers (so we skip files that
        // self-publish).
        let open_canonical: std::collections::HashSet<PathBuf> = {
            let vfs = self.vfs.read();
            vfs.paths().filter_map(|p| p.canonicalize().ok()).collect()
        };

        // Collect the unopened ledger files as (uri, file_id, source, parse).
        // Parses are owned here so they outlive the `ledger_diagnostics_multi`
        // call; sources borrow the held ledger snapshot. Parsing each unopened
        // file is cheap next to the validation we now do only once.
        struct Unopened<'a> {
            path: AbsPathBuf,
            file_id: u16,
            source: &'a str,
            parse: ParseResult,
        }
        let unopened: Vec<Unopened<'_>> = ledger
            .source_map
            .files()
            .iter()
            .filter_map(|f| {
                let canonical = f.path.canonicalize().ok();
                // Skip the current file and any open buffer — those self-publish.
                if canonical.as_deref() == current_canonical {
                    return None;
                }
                if let Some(c) = &canonical
                    && open_canonical.contains(c)
                {
                    return None;
                }
                // The path is carried, not a URI: it is what the diagnostics
                // are keyed by, and it is only converted at the moment of
                // sending. Encoding is `crate::proto`'s problem alone.
                //
                // The loader records absolute paths, so this holds; a relative
                // one could not be a diagnostics key and has no URI either.
                let path = match crate::AbsPathBuf::new(f.path.clone()) {
                    Ok(p) => p,
                    Err(e) => {
                        tracing::warn!(
                            "cross-file diagnostics: {} from the source map is unusable: {e}",
                            f.path.display()
                        );
                        return None;
                    }
                };
                Some(Unopened {
                    path,
                    file_id: f.id as u16,
                    source: f.source.as_ref(),
                    parse: parse(&f.source),
                })
            })
            .collect();

        // Targets for the single validation. When the current buffer is part
        // of the ledger it is targets[0] (its diagnostics come from the same
        // validation); when it is NOT (`current_file_id == None`, e.g. a
        // scratch buffer) only the unopened files are validated here and the
        // caller handles the current buffer via the single-file path.
        let has_current_target = current_file_id.is_some();
        let mut targets: Vec<crate::handlers::diagnostics::FileDiagTarget<'_>> =
            Vec::with_capacity(usize::from(has_current_target) + unopened.len());
        if let Some(current_fid) = current_file_id {
            targets.push(crate::handlers::diagnostics::FileDiagTarget {
                file_id: current_fid,
                source: current_source,
                parse: current_parse,
            });
        }
        targets.extend(
            unopened
                .iter()
                .map(|u| crate::handlers::diagnostics::FileDiagTarget {
                    file_id: u.file_id,
                    source: u.source,
                    parse: &u.parse,
                }),
        );

        let mut per_file = crate::handlers::diagnostics::ledger_diagnostics_multi(
            ledger_state,
            overlay,
            &targets,
            self.position_encoding,
        );

        // If present, per_file[0] is the current file; the rest align 1:1
        // with `unopened`.
        let current_diags = if has_current_target && !per_file.is_empty() {
            per_file.remove(0)
        } else {
            Vec::new()
        };
        let cross_file: Vec<(AbsPathBuf, Vec<lsp_types::Diagnostic>)> = unopened
            .into_iter()
            .zip(per_file)
            .map(|(u, diags)| (u.path, diags))
            .collect();
        (current_diags, cross_file)
    }

    /// Publish or clear diagnostics for unopened included files.
    ///
    /// Non-empty sets are published and their paths tracked in
    /// [`MainLoopState::cross_file_diag_paths`]. Any previously-tracked path
    /// that is NOT erroring this round is then explicitly cleared (empty
    /// publish) and untracked — this covers a fixed error, an include-graph
    /// change, the ledger becoming single-file/unavailable (so `cross_file` is
    /// empty), all of which would otherwise leave stale errors in the client.
    /// Files currently open in a buffer are left alone: those buffers publish
    /// (and clear) their own diagnostics via didOpen/didChange/didClose.
    fn publish_cross_file_diagnostics(
        &mut self,
        cross_file: Vec<(AbsPathBuf, Vec<lsp_types::Diagnostic>)>,
    ) {
        // Publish the files that have errors this round.
        let mut erroring: std::collections::HashSet<AbsPathBuf> = std::collections::HashSet::new();
        for (path, diags) in cross_file {
            if diags.is_empty() {
                continue;
            }
            erroring.insert(path.clone());
            self.cross_file_diag_paths.insert(path.clone());
            self.diagnostics.insert(path.clone(), diags.clone());
            self.send_diagnostics(&path, diags);
        }

        // Clear any previously-tracked file that is no longer erroring and is
        // not currently open (open buffers manage their own diagnostics).
        //
        // Compared in the LOADER's spelling on both sides. `cross_file_diag_paths`
        // holds `source_map` paths, which `DiskFileSystem::normalize` has
        // canonicalized; VFS paths come from the client's URI and are
        // deliberately never canonicalized. Those two are not the same string
        // for the same file — guaranteed on Windows, where `canonicalize`
        // always returns the `\\?\` verbatim form, and reachable on macOS
        // through case or a symlinked ledger directory.
        //
        // An earlier version compared them raw, so a file the user had just
        // OPENED failed the "is it open" test, was judged stale, and had its
        // real errors cleared out from under a live buffer. The three sibling
        // source-map cross-references in this file all canonicalize first;
        // this one was the exception.
        //
        // A path that no longer resolves yields `None` and is treated as not
        // open, which is right: a deleted file's diagnostics should clear.
        let open_canonical: std::collections::HashSet<PathBuf> = self
            .vfs
            .read()
            .paths()
            .filter_map(|p| AbsPathBuf::new(p.clone()).ok())
            .filter_map(|p| p.canonical_for_loader_lookup())
            .collect();
        let stale: Vec<AbsPathBuf> = self
            .cross_file_diag_paths
            .iter()
            .filter(|p| {
                !erroring.contains(*p)
                    && !p
                        .canonical_for_loader_lookup()
                        .is_some_and(|c| open_canonical.contains(&c))
            })
            .cloned()
            .collect();
        for path in stale {
            self.cross_file_diag_paths.remove(&path);
            self.diagnostics.remove(&path);
            self.send_diagnostics(&path, vec![]);
        }
    }

    /// Send diagnostics for a path, converting to a URI at the wire.
    ///
    /// A path with no representable `file:` URI cannot be addressed to the
    /// client at all, so the only options are to warn or to lie; this warns.
    fn send_diagnostics(&self, path: &std::path::Path, diagnostics: Vec<lsp_types::Diagnostic>) {
        match crate::path_to_uri(path) {
            Ok(uri) => self.send_diagnostics_to_uri(&uri, diagnostics),
            Err(e) => tracing::warn!(
                "no file URI for {}: {e}; cannot publish {} diagnostic(s)",
                path.display(),
                diagnostics.len()
            ),
        }
    }

    /// Send diagnostics to a URI the client itself supplied.
    ///
    /// Used on the request path, where echoing the client's own spelling back
    /// is what its diagnostic store is keyed by.
    fn send_diagnostics_to_uri(&self, uri: &Uri, diagnostics: Vec<lsp_types::Diagnostic>) {
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
        // Wake for the earliest debounced diagnostics pass, or never when
        // none is pending. Rebuilt every iteration because each event can
        // move it (a `didChange` pushes its document's deadline back).
        let diagnostics_timer = match state.next_diagnostics_deadline() {
            Some(deadline) => crossbeam_channel::at(deadline),
            None => crossbeam_channel::never(),
        };
        crossbeam_channel::select! {
            recv(receiver) -> msg => {
                let msg = match msg {
                    Ok(msg) => msg,
                    Err(_) => break 0, // Channel closed without an `exit` notification.
                };
                state.handle_event(message_event(msg));
            }
            recv(task_receiver) -> task_result => {
                if let Ok(result) = task_result {
                    state.handle_event(Event::Task(result));
                }
            }
            recv(diagnostics_timer) -> _ => {
                state.on_diagnostics_timer(&receiver);
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

/// Wrap a raw client message as a main-loop event.
fn message_event(msg: lsp_server::Message) -> Event {
    match msg {
        lsp_server::Message::Request(req) => Event::Message(Message::Request(req)),
        lsp_server::Message::Notification(notif) => Event::Message(Message::Notification(notif)),
        lsp_server::Message::Response(resp) => Event::Message(Message::Response(resp)),
    }
}

impl MainLoopState {
    /// The diagnostics timer fired: drain what the client has already sent,
    /// then run the passes that are still due.
    ///
    /// Draining first is what collapses a backlog. When a pass is slow, the
    /// client's next edits pile up in the channel behind it; handling them
    /// before deciding pushes their document's deadline back, so the backlog
    /// costs one pass after it rather than one pass per queued edit. Only the
    /// messages queued at this moment are drained, so a client that never
    /// stops sending cannot keep the loop in here.
    fn on_diagnostics_timer(&mut self, receiver: &Receiver<lsp_server::Message>) {
        for _ in 0..receiver.len() {
            let Ok(msg) = receiver.try_recv() else {
                // Empty or disconnected: the main loop's `recv` arm sees the
                // disconnect on its next iteration and ends the loop.
                break;
            };
            self.handle_event(message_event(msg));
            if self.pending_exit_code.is_some() {
                return;
            }
        }
        self.run_due_diagnostics();
    }
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

    /// A root probed once must not be re-loaded for every file opened.
    ///
    /// Probing costs a full ledger load, and the upward search runs on every
    /// `didOpen` until something is adopted, so a stray `main.beancount` over
    /// an unrelated ledger was re-loaded and re-rejected once per file. On a
    /// 900KB ledger that measured as three loads for three opens; with the
    /// memo it is one.
    ///
    /// This asserts the memo is populated once and cleared by an edit. The
    /// SKIP itself is a `continue` on that set, and its effect was measured
    /// (0.06s then 0.00s per open, and one "Loading journal file" line instead
    /// of three) rather than asserted here.
    #[test]
    fn an_unrelated_root_is_probed_once_not_once_per_file() {
        let (sender, _receiver) = crossbeam_channel::unbounded();
        let mut state = MainLoopState::new(sender, None);

        let dir = std::env::temp_dir().join(format!("rl-reject-{}", std::process::id()));
        let _ = std::fs::remove_dir_all(&dir);
        let work = dir.join("work");
        std::fs::create_dir_all(&work).expect("mkdir");

        // An unrelated ledger with the conventional name, above the files.
        std::fs::write(
            dir.join("leaf.beancount"),
            "2025-01-01 open Assets:Other EUR\n",
        )
        .expect("write leaf");
        let root = dir.join("main.beancount");
        std::fs::write(&root, "include \"leaf.beancount\"\n").expect("write root");

        let open = |state: &mut MainLoopState, n: u32| {
            let f = work.join(format!("f{n}.beancount"));
            let text = "2026-01-01 balance Assets:Cash 0.00 EUR\n".to_string();
            std::fs::write(&f, &text).expect("write file");
            // `format!("file://{}")` is not a URI on Windows: an absolute
            // path there is `C:\...`, which does not parse.
            let uri: Uri = crate::path_to_uri(&f).expect("file URI");
            state.on_did_open(lsp_types::DidOpenTextDocumentParams {
                text_document: lsp_types::TextDocumentItem {
                    uri,
                    language_id: "beancount".to_string(),
                    version: 1,
                    text,
                },
            });
        };

        open(&mut state, 1);
        let after_first = state.probed_roots.len();
        open(&mut state, 2);
        open(&mut state, 3);

        assert_eq!(
            after_first, 1,
            "the unrelated root should have been probed exactly once"
        );
        assert_eq!(
            state.probed_roots.len(),
            1,
            "later opens re-probed instead of consulting the cache: {:?}",
            state.probed_roots.keys().collect::<Vec<_>>()
        );
        // It loaded fine, it just does not reach these files. Recording that
        // as a flat rejection is what made a root unadoptable for ITSELF.
        assert!(
            state
                .probed_roots
                .get(&root)
                .expect("the root must be in the cache")
                .is_some(),
            "a root that loads must cache what it reaches, not a bare rejection"
        );
        assert!(
            state.journal_file.is_none(),
            "an unrelated root was adopted: {:?}",
            state.journal_file
        );

        // An edit is what could make a root start including a file it did
        // not before, so the cache must not outlive one.
        let changed: Uri = crate::path_to_uri(&root).expect("file URI");
        state.on_did_change_watched_files(lsp_types::DidChangeWatchedFilesParams {
            changes: vec![lsp_types::FileEvent {
                uri: changed,
                typ: lsp_types::FileChangeType::CHANGED,
            }],
        });
        assert!(
            state.probed_roots.is_empty(),
            "a watched-file change must retire the cache: {:?}",
            state.probed_roots.keys().collect::<Vec<_>>()
        );

        let _ = std::fs::remove_dir_all(&dir);
    }

    /// Opening a cross-published file hands its diagnostics to the buffer.
    ///
    /// While unopened, an included file's errors are published under the URI
    /// the SERVER builds from the loader's canonical path. Once open, the
    /// buffer publishes under the URI the CLIENT sent. Those differ whenever
    /// the ledger is reached through a symlink or a differently-cased path, and
    /// a client keys its diagnostic store by URI — so the stale set stays on
    /// screen for a file the user can see is open, next to the live one.
    ///
    /// `publish_cross_file_diagnostics` cannot clean this up: it skips files
    /// that are open, so it stops touching the entry precisely when the entry
    /// becomes wrong.
    #[test]
    fn opening_a_cross_published_file_clears_its_server_side_diagnostics() {
        let (sender, receiver) = crossbeam_channel::unbounded();
        let mut state = MainLoopState::new(sender, None);

        // A real file, so the loader spelling resolves on every platform.
        let dir = std::env::temp_dir().join(format!("rl-xfile-{}", std::process::id()));
        let _ = std::fs::remove_dir_all(&dir);
        std::fs::create_dir_all(&dir).expect("mkdir");
        let file = dir.join("included.beancount");
        std::fs::write(&file, "2024-01-01 open Assets:Cash USD\n").expect("write");

        // What the cross-file publisher would have left: an entry keyed by the
        // canonical path, published under the canonical URI.
        let canonical =
            crate::AbsPathBuf::new(file.canonicalize().expect("canon")).expect("absolute");
        state.diagnostics.insert(canonical.clone(), vec![]);
        state.cross_file_diag_paths.insert(canonical.clone());
        while receiver.try_recv().is_ok() {} // drain setup noise

        // The client opens it under its own spelling — the uncanonicalized
        // path, which is what an editor actually sends.
        let uri = crate::path_to_uri(&file).expect("uri");
        state.on_did_open(lsp_types::DidOpenTextDocumentParams {
            text_document: lsp_types::TextDocumentItem {
                uri,
                language_id: "beancount".to_string(),
                version: 1,
                text: "2024-01-01 open Assets:Cash USD\n".to_string(),
            },
        });

        assert!(
            state.cross_file_diag_paths.is_empty(),
            "the tracked entry must be released: {:?}",
            state.cross_file_diag_paths
        );

        // And an explicit empty publish must have gone out under the URI the
        // old set was published under, or the client keeps showing it.
        let canonical_uri = crate::path_to_uri(canonical.as_path()).expect("uri");
        let mut cleared = false;
        while let Ok(msg) = receiver.try_recv() {
            if let lsp_server::Message::Notification(n) = msg
                && n.method == "textDocument/publishDiagnostics"
                && let Ok(p) =
                    serde_json::from_value::<lsp_types::PublishDiagnosticsParams>(n.params)
                && p.uri.as_str() == canonical_uri.as_str() // ratchet-allow: uri-string-eq asserting the exact wire spelling
                && p.diagnostics.is_empty()
            {
                cleared = true;
            }
        }
        assert!(cleared, "no clear was sent to {}", canonical_uri.as_str());

        let _ = std::fs::remove_dir_all(&dir);
    }

    /// Closing a document evicts its diagnostics even when the client spells
    /// the URI differently than we do.
    ///
    /// A file has one path but many URIs. Cross-file diagnostics are published
    /// under the URI WE build from the source map; a `didClose` arrives under
    /// the URI the CLIENT built. While the cache was keyed by `Uri` those were
    /// two entries, only one of which the close could reach, so the other
    /// survived with no buffer left to clear it — and the balance code lens
    /// reads exactly that cache for its verdict (#1264), so a closed file's
    /// stale errors kept driving a lens.
    ///
    /// The three spellings below are the same file by every rule in RFC 3986:
    /// a `.` segment, and a percent-encoded character that is unreserved and
    /// so must decode before comparison.
    #[test]
    fn did_close_evicts_diagnostics_across_uri_spellings() {
        // What a cross-file publish would have cached, keyed the way that code
        // path keys it: the path from the source map.
        let path = crate::AbsPathBuf::new(crate::test_abs("tmp/rl-close/ledger.beancount"))
            .expect("test_abs is absolute");
        // Spellings are derived from the canonical URI rather than written out,
        // so they name this path on whatever platform is running.
        let canonical = crate::path_to_uri(&path).expect("canonical uri");
        let dir = canonical
            .as_str()
            .rsplit_once('/')
            .expect("a URI with a directory")
            .0
            .to_string();
        for spelling in [
            format!("{dir}/./ledger.beancount"),
            format!("{dir}/ledger%2Ebeancount"),
            format!("{dir}/sub/../ledger.beancount"),
        ] {
            let (sender, _receiver) = crossbeam_channel::unbounded();
            let mut state = MainLoopState::new(sender, None);
            let path = path.clone();
            state.diagnostics.insert(path.clone(), vec![]);
            state.cross_file_diag_paths.insert(path.clone());

            let uri: Uri = spelling.parse().expect("test URI parses");
            state.on_did_close(lsp_types::DidCloseTextDocumentParams {
                text_document: lsp_types::TextDocumentIdentifier { uri },
            });

            assert!(
                state.diagnostics.is_empty(),
                "{spelling} left the cache populated: {:?}",
                state.diagnostics.keys().collect::<Vec<_>>()
            );
            assert!(
                state.cross_file_diag_paths.is_empty(),
                "{spelling} left the cross-file set populated"
            );
        }
    }

    /// Debounced diagnostics (#2940). Time is a hand-advanced clock, never
    /// the wall clock, so these are exact about what is due when.
    mod coalescing {
        use super::*;
        use crate::diagnostics_schedule::DIAGNOSTICS_DEBOUNCE;
        use std::sync::Mutex;
        use std::time::Duration;

        const MS: Duration = Duration::from_millis(1);

        /// A server state whose schedule reads `clock` instead of the wall.
        struct Harness {
            state: MainLoopState,
            receiver: Receiver<lsp_server::Message>,
            clock: Arc<Mutex<Instant>>,
            dir: tempfile::TempDir,
        }

        impl Harness {
            fn new() -> Self {
                let (sender, receiver) = crossbeam_channel::unbounded();
                let mut state = MainLoopState::new(sender, None);
                let clock = Arc::new(Mutex::new(Instant::now()));
                let shared = Arc::clone(&clock);
                state.clock = Box::new(move || *shared.lock().expect("clock lock"));
                Self {
                    state,
                    receiver,
                    clock,
                    dir: tempfile::tempdir().expect("tempdir"),
                }
            }

            fn advance(&self, by: Duration) {
                *self.clock.lock().expect("clock lock") += by;
            }

            fn uri(&self, name: &str) -> Uri {
                crate::path_to_uri(&self.dir.path().join(name)).expect("file uri")
            }

            fn open(&mut self, uri: &Uri, text: &str) {
                self.state
                    .on_did_open(lsp_types::DidOpenTextDocumentParams {
                        text_document: lsp_types::TextDocumentItem {
                            uri: uri.clone(),
                            language_id: "beancount".to_string(),
                            version: 1,
                            text: text.to_string(),
                        },
                    });
            }

            fn change(&mut self, uri: &Uri, version: i32, text: &str) {
                self.state.on_did_change(change_params(uri, version, text));
            }

            /// Every diagnostics publish sent since the last call.
            fn published(&self) -> Vec<lsp_types::PublishDiagnosticsParams> {
                let mut out = Vec::new();
                while let Ok(msg) = self.receiver.try_recv() {
                    if let lsp_server::Message::Notification(n) = msg
                        && n.method == PublishDiagnostics::METHOD
                    {
                        out.push(serde_json::from_value(n.params).expect("publish params"));
                    }
                }
                out
            }
        }

        fn change_params(
            uri: &Uri,
            version: i32,
            text: &str,
        ) -> lsp_types::DidChangeTextDocumentParams {
            lsp_types::DidChangeTextDocumentParams {
                text_document: lsp_types::VersionedTextDocumentIdentifier {
                    uri: uri.clone(),
                    version,
                },
                content_changes: vec![lsp_types::TextDocumentContentChangeEvent {
                    range: None,
                    range_length: None,
                    text: text.to_string(),
                }],
            }
        }

        fn for_doc<'a>(
            published: &'a [lsp_types::PublishDiagnosticsParams],
            uri: &Uri,
        ) -> Vec<&'a lsp_types::PublishDiagnosticsParams> {
            let path = uri_to_path(uri).expect("path");
            published
                .iter()
                .filter(|p| uri_to_path(&p.uri).ok().as_ref() == Some(&path))
                .collect()
        }

        /// Version `n` of a document: one parse error, on line `n`. Every
        /// version's diagnostics differ, so a publish names its version.
        fn version_text(n: usize) -> String {
            format!("{}this line is not beancount\n", "\n".repeat(n))
        }

        /// What an immediate pass over `text` publishes: a fresh server that
        /// just opened it, with no debouncing involved.
        fn reference_diagnostics(name: &str, text: &str) -> Vec<lsp_types::Diagnostic> {
            let mut h = Harness::new();
            let uri = h.uri(name);
            h.open(&uri, text);
            let published = h.published();
            let mine = for_doc(&published, &uri);
            assert_eq!(mine.len(), 1, "didOpen publishes once");
            mine[0].diagnostics.clone()
        }

        /// The distinct lines `p` reports errors on (one bad line can yield
        /// more than one diagnostic).
        fn error_lines(p: &lsp_types::PublishDiagnosticsParams) -> Vec<u32> {
            let mut lines: Vec<u32> = p.diagnostics.iter().map(|d| d.range.start.line).collect();
            lines.dedup();
            lines
        }

        #[test]
        fn test_did_open_publishes_immediately() {
            let mut h = Harness::new();
            let uri = h.uri("a.beancount");
            h.open(&uri, &version_text(0));
            assert_eq!(h.state.diagnostics_passes, 1);
            assert_eq!(for_doc(&h.published(), &uri).len(), 1);
            assert_eq!(h.state.next_diagnostics_deadline(), None);
        }

        #[test]
        fn test_burst_of_changes_runs_one_pass_matching_final_text() {
            const N: usize = 50;
            let mut h = Harness::new();
            let uri = h.uri("a.beancount");
            h.open(&uri, &version_text(0));
            h.published();
            let before = h.state.diagnostics_passes;

            for n in 1..=N {
                h.change(&uri, n as i32 + 1, &version_text(n));
                // Every edit lands at once, so requests see the newest text.
                assert_eq!(h.state.get_document_data(&uri).0, version_text(n));
                h.advance(10 * MS);
                h.state.run_due_diagnostics();
            }
            assert_eq!(
                h.state.diagnostics_passes, before,
                "no pass may run while the edits keep coming"
            );
            assert!(h.published().is_empty());

            // Not yet: the last edit was 10 ms ago.
            h.advance(DIAGNOSTICS_DEBOUNCE - 10 * MS - MS);
            h.state.run_due_diagnostics();
            assert_eq!(h.state.diagnostics_passes, before);

            h.advance(MS);
            h.state.run_due_diagnostics();
            assert_eq!(h.state.diagnostics_passes, before + 1, "exactly one pass");
            let published = h.published();
            let mine = for_doc(&published, &uri);
            assert_eq!(mine.len(), 1, "exactly one publish");
            assert_eq!(
                mine[0].diagnostics,
                reference_diagnostics("a.beancount", &version_text(N)),
                "the pass must describe the final text"
            );

            // Nothing left over.
            assert_eq!(h.state.next_diagnostics_deadline(), None);
            h.advance(DIAGNOSTICS_DEBOUNCE * 10);
            h.state.run_due_diagnostics();
            assert_eq!(h.state.diagnostics_passes, before + 1);
        }

        /// The main loop's timer arm drains changes that are already queued
        /// before it runs anything, so a backlog that piled up behind a slow
        /// pass costs one pass, for its last version.
        #[test]
        fn test_timer_drains_queued_changes_into_one_pass() {
            let mut h = Harness::new();
            let uri = h.uri("a.beancount");
            h.open(&uri, &version_text(0));
            h.change(&uri, 2, &version_text(1));
            h.published();
            let before = h.state.diagnostics_passes;

            // The pass for version 2 is due, but 20 more edits are queued.
            h.advance(DIAGNOSTICS_DEBOUNCE);
            let (client, queue) = crossbeam_channel::unbounded();
            for n in 2..22 {
                let notif = lsp_server::Notification::new(
                    DidChangeTextDocument::METHOD.to_string(),
                    change_params(&uri, n as i32 + 1, &version_text(n)),
                );
                client
                    .send(lsp_server::Message::Notification(notif))
                    .expect("queue");
            }

            h.state.on_diagnostics_timer(&queue);
            assert!(queue.is_empty(), "the queued edits must be drained");
            assert_eq!(
                h.state.diagnostics_passes, before,
                "the drained edits push the deadline back; nothing is due yet"
            );

            h.advance(DIAGNOSTICS_DEBOUNCE);
            h.state.on_diagnostics_timer(&queue);
            assert_eq!(h.state.diagnostics_passes, before + 1);
            let published = h.published();
            let mine = for_doc(&published, &uri);
            assert_eq!(mine.len(), 1);
            assert_eq!(error_lines(mine[0]), vec![21]);
        }

        #[test]
        fn test_interleaved_documents_each_get_their_final_pass() {
            let mut h = Harness::new();
            let a = h.uri("a.beancount");
            let b = h.uri("b.beancount");
            h.open(&a, &version_text(0));
            h.open(&b, &version_text(0));
            h.published();
            let before = h.state.diagnostics_passes;

            for n in 1..=10 {
                h.change(&a, n as i32 + 1, &version_text(n));
                h.advance(10 * MS);
                h.change(&b, n as i32 + 1, &version_text(n + 100));
                h.advance(10 * MS);
            }
            h.advance(DIAGNOSTICS_DEBOUNCE);
            h.state.run_due_diagnostics();

            assert_eq!(h.state.diagnostics_passes, before + 2, "one pass each");
            let published = h.published();
            let pa = for_doc(&published, &a);
            let pb = for_doc(&published, &b);
            assert_eq!(pa.len(), 1);
            assert_eq!(pb.len(), 1);
            assert_eq!(error_lines(pa[0]), vec![10]);
            assert_eq!(error_lines(pb[0]), vec![110]);
        }

        /// Version 2's deadline passes after version 3 has arrived. Nothing
        /// may be published for version 2, then or ever.
        #[test]
        fn test_no_publish_for_an_intermediate_version() {
            let mut h = Harness::new();
            let uri = h.uri("a.beancount");
            h.open(&uri, &version_text(0));
            h.published();

            h.change(&uri, 2, &version_text(2));
            h.advance(DIAGNOSTICS_DEBOUNCE - MS);
            h.change(&uri, 3, &version_text(3));
            h.advance(MS); // version 2's deadline
            h.state.run_due_diagnostics();
            assert!(
                for_doc(&h.published(), &uri).is_empty(),
                "version 2 was superseded before its deadline"
            );

            h.advance(DIAGNOSTICS_DEBOUNCE);
            h.state.run_due_diagnostics();
            let published = h.published();
            let mine = for_doc(&published, &uri);
            assert_eq!(mine.len(), 1);
            assert_eq!(error_lines(mine[0]), vec![3], "only version 3 is published");
        }

        /// The balance code lens reads the diagnostics cache. A request made
        /// while a pass is pending must see the edited text's verdict, not
        /// the one cached before the edit.
        #[test]
        fn test_code_lens_during_pending_pass_sees_current_diagnostics() {
            const PASSING: &str = "2024-01-01 open Assets:Cash USD\n\
                                   2024-01-01 open Equity:Opening USD\n\
                                   2024-01-02 * \"seed\"\n  \
                                   Assets:Cash  100 USD\n  \
                                   Equity:Opening  -100 USD\n\
                                   2024-01-03 balance Assets:Cash 100 USD\n";
            let failing = PASSING.replace("balance Assets:Cash 100", "balance Assets:Cash 50");

            let mut h = Harness::new();
            let uri = h.uri("a.beancount");
            h.open(&uri, PASSING);
            h.change(&uri, 2, &failing);
            h.published();
            assert!(
                h.state.next_diagnostics_deadline().is_some(),
                "pass pending"
            );

            let req = lsp_server::Request::new(
                lsp_server::RequestId::from(7),
                CodeLensRequest::METHOD.to_string(),
                CodeLensParams {
                    text_document: lsp_types::TextDocumentIdentifier { uri: uri.clone() },
                    work_done_progress_params: Default::default(),
                    partial_result_params: Default::default(),
                },
            );
            h.state.handle_request(req);

            let mut lenses: Option<Vec<CodeLens>> = None;
            while let Ok(msg) = h.receiver.try_recv() {
                if let lsp_server::Message::Response(r) = msg {
                    lenses = Some(
                        serde_json::from_value(r.response_result.expect("codeLens ok"))
                            .expect("lenses"),
                    );
                }
            }
            let titles: Vec<String> = lenses
                .expect("a codeLens response")
                .into_iter()
                .filter_map(|l| l.command.map(|c| c.title))
                .filter(|t| t.contains("Balance:"))
                .collect();
            assert_eq!(titles.len(), 1, "{titles:?}");
            assert!(
                titles[0].contains('⚠') && titles[0].contains("50"),
                "the lens must reflect the edited (failing) assertion, got {titles:?}"
            );
            assert_eq!(
                h.state.next_diagnostics_deadline(),
                None,
                "the request settled the pending pass"
            );
        }

        #[test]
        fn test_did_close_during_pending_pass_cancels_and_clears() {
            let mut h = Harness::new();
            let uri = h.uri("a.beancount");
            h.open(&uri, &version_text(0));
            h.change(&uri, 2, &version_text(5));
            h.published();
            let before = h.state.diagnostics_passes;

            h.state.on_did_close(lsp_types::DidCloseTextDocumentParams {
                text_document: lsp_types::TextDocumentIdentifier { uri: uri.clone() },
            });
            assert_eq!(h.state.next_diagnostics_deadline(), None, "pass cancelled");
            let published = h.published();
            let mine = for_doc(&published, &uri);
            assert_eq!(mine.len(), 1, "the close sends one clear");
            assert!(mine[0].diagnostics.is_empty());

            h.advance(DIAGNOSTICS_DEBOUNCE * 2);
            h.state.run_due_diagnostics();
            assert_eq!(h.state.diagnostics_passes, before);
            assert!(
                for_doc(&h.published(), &uri).is_empty(),
                "nothing may be republished for a closed document"
            );
        }

        /// An immediate publish settles a pass pending for the same file. A
        /// watched-file change inside the debounce window revalidates every
        /// open buffer from its current text; the pass the edit scheduled
        /// would only repeat that work.
        #[test]
        fn test_revalidation_settles_a_pending_pass() {
            let mut h = Harness::new();
            let a = h.uri("a.beancount");
            let b = h.uri("b.beancount");
            h.open(&a, &version_text(0));
            h.open(&b, &version_text(0));
            h.change(&a, 2, &version_text(4));
            h.published();
            let before = h.state.diagnostics_passes;

            h.advance(DIAGNOSTICS_DEBOUNCE / 2);
            h.state
                .on_did_change_watched_files(lsp_types::DidChangeWatchedFilesParams {
                    changes: vec![lsp_types::FileEvent {
                        uri: h.uri("other.beancount"),
                        typ: lsp_types::FileChangeType::CHANGED,
                    }],
                });
            assert_eq!(
                h.state.diagnostics_passes,
                before + 2,
                "one per open buffer"
            );
            let published = h.published();
            let pa = for_doc(&published, &a);
            assert_eq!(pa.len(), 1);
            assert_eq!(error_lines(pa[0]), vec![4], "revalidated from current text");
            assert_eq!(
                h.state.next_diagnostics_deadline(),
                None,
                "the revalidation must settle the pass the edit scheduled"
            );

            h.advance(DIAGNOSTICS_DEBOUNCE * 2);
            h.state.run_due_diagnostics();
            assert_eq!(h.state.diagnostics_passes, before + 2, "no redundant pass");
        }

        /// After `shutdown` nothing more may be published, so the passes still
        /// owed are dropped.
        #[test]
        fn test_shutdown_drops_pending_passes() {
            let mut h = Harness::new();
            let uri = h.uri("a.beancount");
            h.open(&uri, &version_text(0));
            h.change(&uri, 2, &version_text(1));
            h.published();
            let before = h.state.diagnostics_passes;

            h.state.handle_request(lsp_server::Request::new(
                lsp_server::RequestId::from(1),
                Shutdown::METHOD.to_string(),
                serde_json::Value::Null,
            ));
            assert_eq!(h.state.next_diagnostics_deadline(), None);
            h.advance(DIAGNOSTICS_DEBOUNCE * 2);
            h.state.run_due_diagnostics();
            assert_eq!(h.state.diagnostics_passes, before);
            assert!(for_doc(&h.published(), &uri).is_empty());
        }

        /// After `shutdown`, document and watched-file notifications are
        /// ignored, so nothing is scheduled or published; `exit` still works.
        #[test]
        fn test_notifications_after_shutdown_are_ignored() {
            let mut h = Harness::new();
            let a = h.uri("a.beancount");
            let b = h.uri("b.beancount");
            let other = h.uri("other.beancount");
            h.open(&a, &version_text(0));
            h.state.handle_request(lsp_server::Request::new(
                lsp_server::RequestId::from(1),
                Shutdown::METHOD.to_string(),
                serde_json::Value::Null,
            ));
            h.published();
            let before = h.state.diagnostics_passes;

            let notify = |h: &mut Harness, method: &str, params: serde_json::Value| {
                h.state
                    .handle_notification(lsp_server::Notification::new(method.to_string(), params));
            };
            notify(
                &mut h,
                DidOpenTextDocument::METHOD,
                serde_json::to_value(lsp_types::DidOpenTextDocumentParams {
                    text_document: lsp_types::TextDocumentItem {
                        uri: b.clone(),
                        language_id: "beancount".to_string(),
                        version: 1,
                        text: version_text(1),
                    },
                })
                .expect("params"),
            );
            notify(
                &mut h,
                DidChangeTextDocument::METHOD,
                serde_json::to_value(change_params(&a, 2, &version_text(2))).expect("params"),
            );
            notify(
                &mut h,
                DidChangeWatchedFiles::METHOD,
                serde_json::to_value(lsp_types::DidChangeWatchedFilesParams {
                    changes: vec![lsp_types::FileEvent {
                        uri: other,
                        typ: lsp_types::FileChangeType::CHANGED,
                    }],
                })
                .expect("params"),
            );

            assert_eq!(h.state.diagnostics_passes, before, "no pass after shutdown");
            assert_eq!(
                h.state.next_diagnostics_deadline(),
                None,
                "nothing scheduled"
            );
            h.advance(DIAGNOSTICS_DEBOUNCE * 2);
            h.state.run_due_diagnostics();
            assert!(h.published().is_empty(), "nothing published after shutdown");
            assert_eq!(
                h.state.get_document_data(&a).0,
                version_text(0),
                "the change was not applied"
            );

            notify(&mut h, "exit", serde_json::Value::Null);
            assert_eq!(h.state.pending_exit_code, Some(0), "exit is still handled");
        }

        /// A `didChange` with no `didOpen` before it is a client protocol
        /// violation, but the server answered it with diagnostics for the
        /// text it was given before debouncing existed, and still does,
        /// immediately: there is no buffer for a deferred pass to read.
        #[test]
        fn test_did_change_without_open_publishes_from_given_text() {
            let mut h = Harness::new();
            let uri = h.uri("a.beancount");
            h.change(&uri, 2, &version_text(3));

            assert_eq!(h.state.diagnostics_passes, 1);
            assert_eq!(h.state.next_diagnostics_deadline(), None);
            let published = h.published();
            let mine = for_doc(&published, &uri);
            assert_eq!(mine.len(), 1);
            assert_eq!(
                mine[0].diagnostics,
                reference_diagnostics("a.beancount", &version_text(3))
            );
        }
    }

    /// Every `textDocument/publishDiagnostics` sent so far, as
    /// `(uri, [(code, 0-based line)])`.
    fn drain_published(
        receiver: &crossbeam_channel::Receiver<lsp_server::Message>,
    ) -> Vec<(String, Vec<(String, u32)>)> {
        let mut published = Vec::new();
        while let Ok(msg) = receiver.try_recv() {
            if let lsp_server::Message::Notification(n) = msg
                && n.method == "textDocument/publishDiagnostics"
            {
                let p: lsp_types::PublishDiagnosticsParams =
                    serde_json::from_value(n.params).expect("publishDiagnostics params");
                let codes = p
                    .diagnostics
                    .iter()
                    .map(|d| {
                        let code = match &d.code {
                            Some(lsp_types::NumberOrString::String(s)) => s.clone(),
                            Some(lsp_types::NumberOrString::Number(n)) => n.to_string(),
                            None => String::new(),
                        };
                        (code, d.range.start.line)
                    })
                    .collect();
                published.push((p.uri.as_str().to_string(), codes));
            }
        }
        published
    }

    /// The codes last published for `path`, or `None` if nothing was.
    fn last_published_for(
        published: &[(String, Vec<(String, u32)>)],
        path: &std::path::Path,
    ) -> Option<Vec<(String, u32)>> {
        let uri = crate::path_to_uri(path).expect("file URI");
        published
            .iter()
            .rev()
            .find(|(u, _)| u.as_str() == uri.as_str()) // ratchet-allow: uri-string-eq comparing what was sent on the wire
            .map(|(_, codes)| codes.clone())
    }

    fn open_doc(state: &mut MainLoopState, path: &std::path::Path, text: &str) {
        state.on_did_open(lsp_types::DidOpenTextDocumentParams {
            text_document: lsp_types::TextDocumentItem {
                uri: crate::path_to_uri(path).expect("file URI"),
                language_id: "beancount".to_string(),
                version: 1,
                text: text.to_string(),
            },
        });
    }

    fn change_doc(state: &mut MainLoopState, path: &std::path::Path, version: i32, text: &str) {
        state.on_did_change(lsp_types::DidChangeTextDocumentParams {
            text_document: lsp_types::VersionedTextDocumentIdentifier {
                uri: crate::path_to_uri(path).expect("file URI"),
                version,
            },
            content_changes: vec![lsp_types::TextDocumentContentChangeEvent {
                range: None,
                range_length: None,
                text: text.to_string(),
            }],
        });
        state.flush_pending_diagnostics(&crate::path_to_uri(path).expect("file URI"));
    }

    fn close_doc(state: &mut MainLoopState, path: &std::path::Path) {
        state.on_did_close(lsp_types::DidCloseTextDocumentParams {
            text_document: lsp_types::TextDocumentIdentifier {
                uri: crate::path_to_uri(path).expect("file URI"),
            },
        });
    }

    /// `b.beancount` for the cross-file tests: it uses `Assets:X` and
    /// `Equity:E` (opened in main) and has one error of its own (`Assets:Q`
    /// is never opened), so what is published for it shows both whether it
    /// was published at all and which view of main it was validated against.
    const B_TEXT: &str = "2024-01-02 * \"t\"\n  Assets:X  1 USD\n  Equity:E  -1 USD\n\
                          2024-01-03 * \"q\"\n  Assets:Q  1 USD\n  Equity:E  -1 USD\n";

    /// What `rledger check` reports in [`B_TEXT`] when main opens its accounts.
    fn b_own() -> Option<Vec<(String, u32)>> {
        Some(vec![("E1001".to_string(), 3)])
    }

    /// A ledger directory holding `main.beancount` (with `main_text`) and
    /// [`B_TEXT`], canonicalized so the paths match the loader's.
    fn ledger_dir(main_text: &str) -> (tempfile::TempDir, PathBuf, PathBuf) {
        let tmp = tempfile::tempdir().expect("tempdir");
        let dir = tmp.path().canonicalize().expect("canonical tempdir");
        let main = dir.join("main.beancount");
        let b = dir.join("b.beancount");
        std::fs::write(&main, main_text).expect("write main");
        std::fs::write(&b, B_TEXT).expect("write b");
        (tmp, main, b)
    }

    const MAIN_ON_DISK: &str = "include \"b.beancount\"\n\
                                2024-01-01 open Assets:X\n\
                                2024-01-01 open Equity:E\n";

    /// One `"` typed into main: the string runs to the next quote and
    /// swallows both `open`s.
    const MAIN_OOPS: &str = "include \"b.beancount\"\n2024-01-01 * \"oops\n\
                             2024-01-01 open Assets:X\n2024-01-01 open Equity:E\n\
                             2024-01-05 * \"z\"\n  Assets:X  1 USD\n  Equity:E  -1 USD\n";

    /// The edited buffer of a multi-file ledger is validated from its text
    /// while it has a parse error, as `rledger check` validates that text
    /// (#2949): its unbalanced transaction is reported on the buffer's line,
    /// and with the `open`s a typed `"` swallowed, it reports exactly what
    /// `check` reports for main on that text.
    ///
    /// The unopened file is validated against main's last clean text (here
    /// the text as loaded), not the broken buffer (#1813): its diagnostics stay its own on every pass, where
    /// validating it against the broken text would put E1001s on it on one
    /// keystroke and take them away on the next.
    #[test]
    fn a_broken_ledger_buffer_is_validated_from_its_text_and_others_from_disk() {
        let (_tmp, main, b) = ledger_dir(MAIN_ON_DISK);
        let (sender, receiver) = crossbeam_channel::unbounded();
        let mut state = MainLoopState::new(sender, Some(main.clone()));
        open_doc(&mut state, &main, MAIN_ON_DISK);
        let published = drain_published(&receiver);
        assert_eq!(last_published_for(&published, &main), Some(vec![]));
        assert_eq!(last_published_for(&published, &b), b_own(), "{published:?}");

        // A line that does not parse, then an unbalanced transaction on line
        // 5 (0-based 4) of the buffer.
        change_doc(
            &mut state,
            &main,
            2,
            "include \"b.beancount\"\ngarbage\n2024-01-01 open Assets:X\n\
             2024-01-01 open Equity:E\n2024-01-03 * \"u\"\n  Assets:X  5 USD\n  \
             Equity:E  -4 USD\n",
        );
        let published = drain_published(&receiver);
        let main_codes = last_published_for(&published, &main).expect("main published");
        assert!(
            main_codes.iter().any(|(c, _)| c.starts_with('P')),
            "the parse error is reported: {main_codes:?}"
        );
        assert!(
            main_codes.contains(&("E3001".to_string(), 4)),
            "the buffer's unbalanced transaction is reported on its line: {main_codes:?}"
        );
        assert_eq!(last_published_for(&published, &b), b_own(), "{published:?}");

        change_doc(&mut state, &main, 3, MAIN_OOPS);
        let published = drain_published(&receiver);
        assert_eq!(
            last_published_for(&published, &main),
            Some(vec![
                ("P0012".to_string(), 4),
                ("E1001".to_string(), 1),
                ("E1001".to_string(), 1),
            ]),
            "the swallowed opens are missed in the buffer, as in check: {published:?}"
        );
        assert_eq!(
            last_published_for(&published, &b),
            b_own(),
            "the unopened file is validated against main as loaded: {published:?}"
        );

        // The edit undone.
        change_doc(&mut state, &main, 4, MAIN_ON_DISK);
        let published = drain_published(&receiver);
        assert_eq!(last_published_for(&published, &main), Some(vec![]));
        assert_eq!(last_published_for(&published, &b), b_own(), "{published:?}");
    }

    /// A main file SAVED with a syntax error is in the ledger as loaded, so
    /// its includes are validated as `rledger check` validates them, and
    /// published on every path that publishes: `didOpen` under a configured
    /// journal, root adoption, and a watched-file change. Nothing waits for
    /// the buffer to parse first.
    #[test]
    fn a_saved_broken_main_still_publishes_its_includes() {
        let main_text = "include \"b.beancount\"\ngarbage\n\
                         2024-01-01 open Assets:X\n2024-01-01 open Equity:E\n";

        // A configured journal.
        let (_tmp, main, b) = ledger_dir(main_text);
        let (sender, receiver) = crossbeam_channel::unbounded();
        let mut state = MainLoopState::new(sender, Some(main.clone()));
        open_doc(&mut state, &main, main_text);
        let published = drain_published(&receiver);
        assert_eq!(
            last_published_for(&published, &main),
            Some(vec![("P0012".to_string(), 1)]),
            "{published:?}"
        );
        assert_eq!(
            last_published_for(&published, &b),
            b_own(),
            "configured journal: {published:?}"
        );

        // A watched-file change: b gains a second error, and is republished.
        std::fs::write(&b, format!("{B_TEXT}2024-01-04 open Assets:X\n")).expect("rewrite b");
        state.on_did_change_watched_files(lsp_types::DidChangeWatchedFilesParams {
            changes: vec![lsp_types::FileEvent {
                uri: crate::path_to_uri(&b).expect("file URI"),
                typ: lsp_types::FileChangeType::CHANGED,
            }],
        });
        let published = drain_published(&receiver);
        let b_codes = last_published_for(&published, &b).expect("b republished");
        assert_eq!(b_codes.len(), 2, "watched-file change: {b_codes:?}");

        // Root adoption: no journal configured, and main declares an include.
        let (_tmp, main, b) = ledger_dir(main_text);
        let (sender, receiver) = crossbeam_channel::unbounded();
        let mut state = MainLoopState::new(sender, None);
        open_doc(&mut state, &main, main_text);
        let published = drain_published(&receiver);
        assert_eq!(
            last_published_for(&published, &b),
            b_own(),
            "root adoption: {published:?}"
        );
    }

    /// A broken buffer changes nothing published for other files, whichever
    /// buffer is edited (#1813). Main is broken by a typed `"` that swallows
    /// the `open`s b uses; editing another, clean, open buffer (c) republishes
    /// b against main's last clean text (here the text as loaded), not
    /// against the broken buffer. Closing main republishes b from disk.
    #[test]
    fn editing_a_clean_buffer_while_another_is_broken_does_not_flap() {
        let main_text = format!("include \"c.beancount\"\n{MAIN_ON_DISK}");
        let main_oops = format!("include \"c.beancount\"\n{MAIN_OOPS}");
        let (_tmp, main, b) = ledger_dir(&main_text);
        let c = main.with_file_name("c.beancount");
        std::fs::write(&c, "2024-01-01 open Assets:C\n").expect("write c");

        let (sender, receiver) = crossbeam_channel::unbounded();
        let mut state = MainLoopState::new(sender, Some(main.clone()));
        open_doc(&mut state, &main, &main_text);
        open_doc(&mut state, &c, "2024-01-01 open Assets:C\n");
        change_doc(&mut state, &main, 2, &main_oops);
        let published = drain_published(&receiver);
        assert_eq!(last_published_for(&published, &b), b_own(), "{published:?}");

        change_doc(
            &mut state,
            &c,
            2,
            "2024-01-01 open Assets:C\n2024-01-01 open Assets:D\n",
        );
        let published = drain_published(&receiver);
        assert_eq!(
            last_published_for(&published, &c),
            Some(vec![]),
            "{published:?}"
        );
        assert_eq!(
            last_published_for(&published, &b),
            b_own(),
            "b is validated against main's last clean text, not its broken buffer: {published:?}"
        );

        close_doc(&mut state, &main);
        let published = drain_published(&receiver);
        assert_eq!(
            last_published_for(&published, &b),
            b_own(),
            "closing main republishes b from disk: {published:?}"
        );
    }

    /// Closing a buffer whose unsaved (clean) text changed another file's
    /// diagnostics republishes that file from disk. Here main's buffer opens
    /// `Assets:Q`, which clears b's own error; once main is closed unsaved,
    /// the error is back.
    #[test]
    fn closing_a_buffer_republishes_the_unopened_files_from_disk() {
        let (_tmp, main, b) = ledger_dir(MAIN_ON_DISK);
        let (sender, receiver) = crossbeam_channel::unbounded();
        let mut state = MainLoopState::new(sender, Some(main.clone()));
        open_doc(&mut state, &main, MAIN_ON_DISK);
        change_doc(
            &mut state,
            &main,
            2,
            &format!("{MAIN_ON_DISK}2024-01-01 open Assets:Q\n"),
        );
        let published = drain_published(&receiver);
        assert_eq!(
            last_published_for(&published, &b),
            Some(vec![]),
            "the buffer's open clears b's error: {published:?}"
        );

        close_doc(&mut state, &main);
        let published = drain_published(&receiver);
        assert_eq!(
            last_published_for(&published, &b),
            b_own(),
            "closed unsaved, main is as on disk again: {published:?}"
        );
    }

    /// A broken buffer's own diagnostics are `rledger check`'s on its text,
    /// plugins included: with `auto_accounts` declared in the buffer, check
    /// (and bean-check) report the syntax error alone, not an E1001 for the
    /// account the plugin opens.
    #[test]
    fn a_broken_buffer_uses_the_plugins_it_declares() {
        let (_tmp, main, _b) = ledger_dir(MAIN_ON_DISK);
        let (sender, receiver) = crossbeam_channel::unbounded();
        let mut state = MainLoopState::new(sender, Some(main.clone()));
        open_doc(&mut state, &main, MAIN_ON_DISK);
        change_doc(
            &mut state,
            &main,
            2,
            "plugin \"beancount.plugins.auto_accounts\"\ninclude \"b.beancount\"\ngarbage\n\
             2024-01-01 open Assets:X\n2024-01-01 open Equity:E\n\
             2024-01-05 * \"z\"\n  Assets:New  1 USD\n  Equity:E  -1 USD\n",
        );
        let published = drain_published(&receiver);
        assert_eq!(
            last_published_for(&published, &main),
            Some(vec![("P0012".to_string(), 2)]),
            "{published:?}"
        );
    }

    /// The #1813 cases: a buffer broken mid-edit recovers a wrong plugin list
    /// (`plugin "auto_acc` swallows the `include` after it into the name) or
    /// none at all (`@@@`). Neither may drop `auto_accounts` from the
    /// validation of the unopened file, which would put E1001s on it.
    #[test]
    fn a_broken_buffer_does_not_drop_its_plugins_from_other_files() {
        let main_text = "plugin \"auto_accounts\"\ninclude \"b.beancount\"\n";
        let tmp = tempfile::tempdir().expect("tempdir");
        let dir = tmp.path().canonicalize().expect("canonical tempdir");
        let main = dir.join("main.beancount");
        let b = dir.join("b.beancount");
        std::fs::write(&main, main_text).expect("write main");
        std::fs::write(
            &b,
            "2024-01-02 * \"x\"\n  Assets:New  10 USD\n  Equity:Opening-Balances  -10 USD\n",
        )
        .expect("write b");

        let (sender, receiver) = crossbeam_channel::unbounded();
        let mut state = MainLoopState::new(sender, Some(main.clone()));
        open_doc(&mut state, &main, main_text);
        drain_published(&receiver);

        for (version, broken) in [
            (2, "plugin \"auto_acc\ninclude \"b.beancount\"\n"),
            (3, "@@@ not valid beancount\n"),
        ] {
            change_doc(&mut state, &main, version, broken);
            let published = drain_published(&receiver);
            let b_codes = last_published_for(&published, &b).unwrap_or_default();
            assert!(
                !b_codes.iter().any(|(c, _)| c == "E1001"),
                "{broken:?}: auto_accounts must still open b's accounts: {published:?}"
            );
        }
    }

    /// Another open buffer with a parse error is validated as loaded, for the
    /// edited buffer as for the unopened files: its unsaved text changes
    /// nothing published for any other file. Here the open buffer `c` opens
    /// `Assets:Z` only in its broken unsaved text, so `main`, which uses it,
    /// reports it unopened, as `rledger check` does with `c` as on disk.
    #[test]
    fn a_broken_other_open_buffer_is_validated_as_loaded() {
        let tmp = tempfile::tempdir().expect("tempdir");
        let dir = tmp.path().canonicalize().expect("canonical tempdir");
        let main = dir.join("main.beancount");
        let c = dir.join("c.beancount");
        let main_on_disk = "include \"c.beancount\"\n2024-01-01 open Equity:E\n";
        std::fs::write(&main, main_on_disk).expect("write main");
        std::fs::write(&c, "2024-01-01 open Assets:Y\n").expect("write c");

        let (sender, receiver) = crossbeam_channel::unbounded();
        let mut state = MainLoopState::new(sender, Some(main.clone()));
        open_doc(&mut state, &main, main_on_disk);
        open_doc(
            &mut state,
            &c,
            "garbage\n2024-01-01 open Assets:Y\n2024-01-01 open Assets:Z\n",
        );
        drain_published(&receiver);

        change_doc(
            &mut state,
            &main,
            2,
            "include \"c.beancount\"\n2024-01-01 open Equity:E\n\
             2024-01-02 * \"t\"\n  Assets:Z  1 USD\n  Equity:E  -1 USD\n",
        );
        let published = drain_published(&receiver);
        assert_eq!(
            last_published_for(&published, &main),
            Some(vec![("E1001".to_string(), 2)]),
            "{published:?}"
        );
    }

    /// What the client shows for `path` after `published`: the last set
    /// sent, or `before` if none was. The cross-file publisher sends an
    /// unopened file's set only when it is non-empty or clears a non-empty
    /// one, so a file that stays clean is not sent anything.
    fn shown_for(
        published: &[(String, Vec<(String, u32)>)],
        path: &std::path::Path,
        before: Vec<(String, u32)>,
    ) -> Vec<(String, u32)> {
        last_published_for(published, path).unwrap_or(before)
    }

    /// Review round 3 of #2949: while a buffer is broken, the clean view
    /// keeps its LAST CLEAN text, not the ledger as loaded. Main's unsaved
    /// clean edit opens `Assets:Q`, which clears b's own error; typing an
    /// unterminated `"` at the end (it swallows nothing) must not undo that
    /// edit for b, and closing the quote leaves b clean too.
    #[test]
    fn a_broken_buffer_keeps_its_last_clean_text_in_the_clean_view() {
        let (_tmp, main, b) = ledger_dir(MAIN_ON_DISK);
        let (sender, receiver) = crossbeam_channel::unbounded();
        let mut state = MainLoopState::new(sender, Some(main.clone()));
        open_doc(&mut state, &main, MAIN_ON_DISK);
        let published = drain_published(&receiver);
        assert_eq!(last_published_for(&published, &b), b_own(), "{published:?}");

        let with_q = format!("{MAIN_ON_DISK}2024-01-01 open Assets:Q\n");
        change_doc(&mut state, &main, 2, &with_q);
        let published = drain_published(&receiver);
        assert_eq!(
            last_published_for(&published, &b),
            Some(vec![]),
            "the buffer's open clears b's error: {published:?}"
        );

        change_doc(
            &mut state,
            &main,
            3,
            &format!("{with_q}2024-01-06 * \"typing"),
        );
        let published = drain_published(&receiver);
        let main_codes = last_published_for(&published, &main).expect("main published");
        assert!(
            main_codes.iter().any(|(c, _)| c.starts_with('P')),
            "main is broken: {main_codes:?}"
        );
        assert_eq!(
            shown_for(&published, &b, vec![]),
            vec![],
            "b is validated against main's last clean text, not as loaded: {published:?}"
        );

        change_doc(
            &mut state,
            &main,
            4,
            &format!("{with_q}2024-01-06 * \"typing\"\n"),
        );
        let published = drain_published(&receiver);
        assert_eq!(last_published_for(&published, &main), Some(vec![]));
        assert_eq!(shown_for(&published, &b, vec![]), vec![], "{published:?}");
    }

    /// [`MAIN_ON_DISK`] with `Assets:Q` opened too, so b is clean.
    const MAIN_WITH_Q: &str = "include \"b.beancount\"\n\
                               2024-01-01 open Assets:X\n\
                               2024-01-01 open Equity:E\n\
                               2024-01-01 open Assets:Q\n";

    /// Main with the `Assets:Q` open removed and a line that does not parse
    /// (0-based line 1).
    const MAIN_BROKEN_NO_Q: &str = "include \"b.beancount\"\ngarbage\n\
                                    2024-01-01 open Assets:X\n\
                                    2024-01-01 open Equity:E\n";

    /// Tell `state` that `path` changed on disk.
    fn disk_changed(state: &mut MainLoopState, path: &std::path::Path) {
        state.on_did_change_watched_files(lsp_types::DidChangeWatchedFilesParams {
            changes: vec![lsp_types::FileEvent {
                uri: crate::path_to_uri(path).expect("file URI"),
                typ: lsp_types::FileChangeType::CHANGED,
            }],
        });
    }

    /// Review round 5 of #2949: a buffer SAVED broken is as loaded. Main is
    /// opened clean (with `Assets:Q`), then broken while dropping that open;
    /// until it is saved, b is validated against main's last clean text and
    /// stays clean. Once the broken text is saved and the ledger reloaded,
    /// b gets the E1001 `rledger check` reports for the ledger on disk,
    /// and keeps it while main stays broken.
    #[test]
    fn a_buffer_saved_broken_is_validated_as_loaded() {
        let (_tmp, main, b) = ledger_dir(MAIN_WITH_Q);
        let (sender, receiver) = crossbeam_channel::unbounded();
        let mut state = MainLoopState::new(sender, Some(main.clone()));
        open_doc(&mut state, &main, MAIN_WITH_Q);
        let published = drain_published(&receiver);
        assert_eq!(last_published_for(&published, &main), Some(vec![]));
        let mut b_shown = shown_for(&published, &b, vec![]);
        assert_eq!(b_shown, vec![], "{published:?}");

        change_doc(&mut state, &main, 2, MAIN_BROKEN_NO_Q);
        let published = drain_published(&receiver);
        assert_eq!(
            last_published_for(&published, &main),
            Some(vec![("P0012".to_string(), 1)]),
            "{published:?}"
        );
        b_shown = shown_for(&published, &b, b_shown);
        assert_eq!(
            b_shown,
            vec![],
            "unsaved: main's last clean text: {published:?}"
        );

        std::fs::write(&main, MAIN_BROKEN_NO_Q).expect("save main");
        disk_changed(&mut state, &main);
        let published = drain_published(&receiver);
        let on_disk = check_codes(
            &[
                ("main.beancount", MAIN_BROKEN_NO_Q),
                ("b.beancount", B_TEXT),
            ],
            "b.beancount",
        );
        assert_eq!(Some(on_disk.clone()), b_own(), "the reference itself");
        b_shown = shown_for(&published, &b, b_shown);
        assert_eq!(
            sorted(b_shown.clone()),
            on_disk,
            "saved: as check: {published:?}"
        );
        assert_eq!(
            last_published_for(&published, &main),
            Some(vec![("P0012".to_string(), 1)]),
            "{published:?}"
        );

        // Still broken after a further edit: the file stays as loaded.
        change_doc(
            &mut state,
            &main,
            3,
            &format!("{MAIN_BROKEN_NO_Q}more garbage\n"),
        );
        let published = drain_published(&receiver);
        b_shown = shown_for(&published, &b, b_shown);
        assert_eq!(sorted(b_shown), on_disk, "{published:?}");
    }

    /// Diagnostic codes with their 0-based lines.
    type Codes = Vec<(String, u32)>;

    /// Save main broken, as [`a_buffer_saved_broken_is_validated_as_loaded`]
    /// does, with main's disk bytes `on_disk(text)` and its buffer
    /// `in_buffer(text)`, and return what b shows after the reload and what
    /// `check` reports for b on disk.
    fn b_after_saving_main_broken(
        on_disk: impl Fn(&str) -> String,
        in_buffer: impl Fn(&str) -> String,
    ) -> (Codes, Codes) {
        let (_tmp, main, b) = ledger_dir(&on_disk(MAIN_WITH_Q));
        let (sender, receiver) = crossbeam_channel::unbounded();
        let mut state = MainLoopState::new(sender, Some(main.clone()));
        open_doc(&mut state, &main, &in_buffer(MAIN_WITH_Q));
        let published = drain_published(&receiver);
        let mut b_shown = shown_for(&published, &b, vec![]);
        assert_eq!(b_shown, vec![], "{published:?}");

        change_doc(&mut state, &main, 2, &in_buffer(MAIN_BROKEN_NO_Q));
        let published = drain_published(&receiver);
        b_shown = shown_for(&published, &b, b_shown);
        assert_eq!(b_shown, vec![], "unsaved: {published:?}");

        std::fs::write(&main, on_disk(MAIN_BROKEN_NO_Q)).expect("save main");
        disk_changed(&mut state, &main);
        let published = drain_published(&receiver);
        let check = check_codes(
            &[
                ("main.beancount", &on_disk(MAIN_BROKEN_NO_Q)),
                ("b.beancount", B_TEXT),
            ],
            "b.beancount",
        );
        (sorted(shown_for(&published, &b, b_shown)), check)
    }

    /// Review round 6 of #2949: the loader keeps a file's leading BOM, and an
    /// editor sends the buffer without it. Main saved broken with a BOM is
    /// still the text the buffer holds, so b gets what `check` reports.
    #[test]
    fn a_buffer_saved_broken_with_a_bom_is_validated_as_loaded() {
        let (shown, check) =
            b_after_saving_main_broken(|text| format!("{}{text}", bom::BOM), str::to_string);
        assert_eq!(Some(check.clone()), b_own(), "the reference itself");
        assert_eq!(shown, check);
    }

    /// The same with CRLF line endings, which the buffer and the disk share.
    #[test]
    fn a_buffer_saved_broken_with_crlf_is_validated_as_loaded() {
        let crlf = |text: &str| text.replace('\n', "\r\n");
        let (shown, check) = b_after_saving_main_broken(crlf, crlf);
        assert_eq!(Some(check.clone()), b_own(), "the reference itself");
        assert_eq!(shown, check);
    }

    /// The other half of the round-5 rule: a reload that reads a text other
    /// than the buffer's (the buffer was edited past what was saved) leaves
    /// the buffer its last clean parse, so b stays validated against it.
    #[test]
    fn a_buffer_edited_past_its_saved_text_keeps_its_last_clean_text() {
        let (_tmp, main, b) = ledger_dir(MAIN_WITH_Q);
        let (sender, receiver) = crossbeam_channel::unbounded();
        let mut state = MainLoopState::new(sender, Some(main.clone()));
        open_doc(&mut state, &main, MAIN_WITH_Q);
        let published = drain_published(&receiver);
        let mut b_shown = shown_for(&published, &b, vec![]);
        assert_eq!(b_shown, vec![], "{published:?}");

        change_doc(&mut state, &main, 2, MAIN_BROKEN_NO_Q);
        std::fs::write(&main, format!("{MAIN_BROKEN_NO_Q}; saved earlier\n")).expect("save main");
        disk_changed(&mut state, &main);
        let published = drain_published(&receiver);
        assert_eq!(
            last_published_for(&published, &main),
            Some(vec![("P0012".to_string(), 1)]),
            "{published:?}"
        );
        b_shown = shown_for(&published, &b, b_shown);
        assert_eq!(b_shown, vec![], "main's last clean text: {published:?}");
    }

    /// A ledger whose main includes `b` (which uses two accounts it never
    /// opens, so each is an E1001 on its line 0 unless `auto_accounts` is
    /// declared) and `c`; main and c are open.
    fn plugin_ledger() -> (tempfile::TempDir, PathBuf, PathBuf, PathBuf) {
        let tmp = tempfile::tempdir().expect("tempdir");
        let dir = tmp.path().canonicalize().expect("canonical tempdir");
        let main = dir.join("main.beancount");
        let b = dir.join("b.beancount");
        let c = dir.join("c.beancount");
        std::fs::write(&main, PLUGIN_MAIN_ON_DISK).expect("write main");
        std::fs::write(
            &b,
            "2024-01-02 * \"x\"\n  Assets:New  10 USD\n  Equity:New  -10 USD\n",
        )
        .expect("write b");
        std::fs::write(&c, "2024-01-01 open Assets:C\n").expect("write c");
        (tmp, main, b, c)
    }

    const PLUGIN_MAIN_ON_DISK: &str = "include \"b.beancount\"\ninclude \"c.beancount\"\n";

    fn b_unopened_twice() -> Option<Vec<(String, u32)>> {
        Some(vec![("E1001".to_string(), 0), ("E1001".to_string(), 0)])
    }

    /// Review round 3 of #2949: the clean view's plugins are those of every
    /// buffer in it, not only of the buffer being published. Main's unsaved
    /// `plugin "auto_accounts"` opens b's accounts whichever open buffer's
    /// pass publishes b, and until main itself is closed.
    #[test]
    fn the_clean_view_takes_every_clean_buffers_plugins() {
        let (_tmp, main, b, c) = plugin_ledger();
        let (sender, receiver) = crossbeam_channel::unbounded();
        let mut state = MainLoopState::new(sender, Some(main.clone()));
        open_doc(&mut state, &main, PLUGIN_MAIN_ON_DISK);
        open_doc(&mut state, &c, "2024-01-01 open Assets:C\n");
        let published = drain_published(&receiver);
        assert_eq!(
            last_published_for(&published, &b),
            b_unopened_twice(),
            "{published:?}"
        );

        change_doc(
            &mut state,
            &main,
            2,
            &format!("plugin \"auto_accounts\"\n{PLUGIN_MAIN_ON_DISK}"),
        );
        let published = drain_published(&receiver);
        assert_eq!(
            last_published_for(&published, &b),
            Some(vec![]),
            "main's unsaved plugin opens b's accounts: {published:?}"
        );

        change_doc(
            &mut state,
            &c,
            2,
            "2024-01-01 open Assets:C\n2024-01-01 open Assets:D\n",
        );
        let published = drain_published(&receiver);
        assert_eq!(
            shown_for(&published, &b, vec![]),
            vec![],
            "editing c publishes b with main's plugin too: {published:?}"
        );

        close_doc(&mut state, &c);
        let published = drain_published(&receiver);
        assert_eq!(
            shown_for(&published, &b, vec![]),
            vec![],
            "closing c keeps main's plugin: {published:?}"
        );

        close_doc(&mut state, &main);
        let published = drain_published(&receiver);
        assert_eq!(
            last_published_for(&published, &b),
            b_unopened_twice(),
            "closing main unsaved drops its plugin: {published:?}"
        );
    }

    /// One revalidation publishes the unopened file once per open buffer,
    /// and every one of those publishes must say the same thing: the clean
    /// view does not depend on which buffer's pass computed it. b is
    /// unbalanced here, so it has an error with or without main's plugin and
    /// every pass sends it.
    #[test]
    fn a_revalidation_publishes_each_file_the_same_way_every_time() {
        let (_tmp, main, b, c) = plugin_ledger();
        std::fs::write(
            &b,
            "2024-01-02 * \"x\"\n  Assets:New  10 USD\n  Equity:New  -9 USD\n",
        )
        .expect("write b");
        let (sender, receiver) = crossbeam_channel::unbounded();
        let mut state = MainLoopState::new(sender, Some(main.clone()));
        open_doc(&mut state, &main, PLUGIN_MAIN_ON_DISK);
        open_doc(&mut state, &c, "2024-01-01 open Assets:C\n");
        change_doc(
            &mut state,
            &main,
            2,
            &format!("plugin \"auto_accounts\"\n{PLUGIN_MAIN_ON_DISK}"),
        );
        drain_published(&receiver);

        state.revalidate_open_documents();
        let published = drain_published(&receiver);
        let b_uri = crate::path_to_uri(&b).expect("file URI");
        let for_b: Vec<&Vec<(String, u32)>> = published
            .iter()
            .filter(|(u, _)| u.as_str() == b_uri.as_str()) // ratchet-allow: uri-string-eq comparing what was sent on the wire
            .map(|(_, codes)| codes)
            .collect();
        assert!(
            for_b.len() >= 2,
            "b is published by both buffers' passes: {published:?}"
        );
        assert!(
            for_b.iter().all(|codes| *codes == for_b[0]),
            "every publish of b agrees: {published:?}"
        );
        assert!(
            !for_b[0].iter().any(|(code, _)| code == "E1001"),
            "with main's plugin: {published:?}"
        );
    }

    const RENAME_ACCOUNTS: &str = "beancount_reds_plugins.rename_accounts.rename_accounts";

    /// A `rename_accounts` line renaming `from` to `to`. Two of them chain
    /// (`A -> B`, `B -> C`) only when they run in that order, so they pin the
    /// order a view's plugins run in.
    fn rename_line(from: &str, to: &str) -> String {
        format!("plugin \"{RENAME_ACCOUNTS}\" \"{{'{from}': '{to}'}}\"\n")
    }

    /// A transaction on `Expenses:A`, which only the chain `A -> B -> C`
    /// takes to the opened `Expenses:C`.
    const RENAMED_TXN: &str = "2024-01-02 * \"x\"\n  Expenses:A  1 USD\n  Assets:Cash  -1 USD\n";

    /// What `rledger check` reports for `target` once `files` (name, text;
    /// `main.beancount` is the root) are saved, as `(code, 0-based line)`,
    /// sorted. It is the reference the LSP's publishes are compared with.
    fn check_codes(files: &[(&str, &str)], target: &str) -> Vec<(String, u32)> {
        let tmp = tempfile::tempdir().expect("tempdir");
        let dir = tmp.path().canonicalize().expect("canonical tempdir");
        for (name, text) in files {
            std::fs::write(dir.join(name), text).expect("write ledger file");
        }
        let ledger = rustledger_loader::load(
            &dir.join("main.beancount"),
            &rustledger_loader::LoadOptions::default(),
        )
        .expect("load");
        let mut codes: Vec<(String, u32)> = ledger
            .errors
            .iter()
            .filter_map(|e| {
                let loc = e.location.as_ref()?;
                (loc.file.file_name()? == target).then(|| {
                    let line = u32::try_from(loc.line).expect("line fits u32") - 1;
                    (e.code.clone(), line)
                })
            })
            .collect();
        codes.sort();
        codes
    }

    fn sorted(mut codes: Vec<(String, u32)>) -> Vec<(String, u32)> {
        codes.sort();
        codes
    }

    /// Review round 4 of #2949: a buffer's plugins run where `check` runs
    /// them, by file and then declaration, not after those of the files the
    /// ledger loaded. b declares `B -> C`; main's unsaved `A -> B` runs
    /// first, as it does in `check` once main is saved, so b's `Expenses:A`
    /// ends up as the opened `Expenses:C`.
    #[test]
    fn a_buffers_plugins_run_in_checks_order() {
        let tmp = tempfile::tempdir().expect("tempdir");
        let dir = tmp.path().canonicalize().expect("canonical tempdir");
        let main = dir.join("main.beancount");
        let b = dir.join("b.beancount");
        let main_on_disk = "include \"b.beancount\"\n";
        let b_text = format!(
            "{}2024-01-01 open Expenses:C\n2024-01-01 open Assets:Cash\n{RENAMED_TXN}",
            rename_line("Expenses:B", "Expenses:C")
        );
        std::fs::write(&main, main_on_disk).expect("write main");
        std::fs::write(&b, &b_text).expect("write b");

        let on_disk = check_codes(
            &[("main.beancount", main_on_disk), ("b.beancount", &b_text)],
            "b.beancount",
        );
        assert_eq!(on_disk, [("E1001".to_string(), 3)], "Expenses:A unopened");

        let (sender, receiver) = crossbeam_channel::unbounded();
        let mut state = MainLoopState::new(sender, Some(main.clone()));
        open_doc(&mut state, &main, main_on_disk);
        let published = drain_published(&receiver);
        let shown = sorted(shown_for(&published, &b, vec![]));
        assert_eq!(shown, on_disk, "{published:?}");

        let main_unsaved = format!("{}{main_on_disk}", rename_line("Expenses:A", "Expenses:B"));
        change_doc(&mut state, &main, 2, &main_unsaved);
        let published = drain_published(&receiver);
        let saved = check_codes(
            &[("main.beancount", &main_unsaved), ("b.beancount", &b_text)],
            "b.beancount",
        );
        assert_eq!(saved, [], "A -> B -> C opens it");
        assert_eq!(
            sorted(shown_for(&published, &b, shown)),
            saved,
            "the LSP agrees with check on the saved texts: {published:?}"
        );
    }

    /// Review round 4 of #2949: the clean view's plugins run in `check`'s
    /// order whichever buffer's pass computes it. Main's unsaved `A -> B` and
    /// c's unsaved `B -> C` are both buffers' (neither file has a stored
    /// plugin); editing either buffer, and one revalidation of both, publish
    /// b as `check` reports it once both are saved.
    #[test]
    fn the_clean_views_plugin_order_does_not_depend_on_the_published_buffer() {
        let tmp = tempfile::tempdir().expect("tempdir");
        let dir = tmp.path().canonicalize().expect("canonical tempdir");
        let main = dir.join("main.beancount");
        let b = dir.join("b.beancount");
        let c = dir.join("c.beancount");
        let main_on_disk = "include \"b.beancount\"\ninclude \"c.beancount\"\n";
        let b_text =
            format!("2024-01-01 open Expenses:C\n2024-01-01 open Assets:Cash\n{RENAMED_TXN}");
        let c_on_disk = "2024-01-01 open Assets:Other\n";
        std::fs::write(&main, main_on_disk).expect("write main");
        std::fs::write(&b, &b_text).expect("write b");
        std::fs::write(&c, c_on_disk).expect("write c");

        let main_unsaved = format!("{}{main_on_disk}", rename_line("Expenses:A", "Expenses:B"));
        let c_unsaved = format!("{}{c_on_disk}", rename_line("Expenses:B", "Expenses:C"));
        let saved = check_codes(
            &[
                ("main.beancount", &main_unsaved),
                ("b.beancount", &b_text),
                ("c.beancount", &c_unsaved),
            ],
            "b.beancount",
        );
        assert_eq!(saved, [], "A -> B -> C opens it");
        let on_disk = check_codes(
            &[
                ("main.beancount", main_on_disk),
                ("b.beancount", &b_text),
                ("c.beancount", c_on_disk),
            ],
            "b.beancount",
        );
        assert_eq!(on_disk, [("E1001".to_string(), 2)], "Expenses:A unopened");

        let (sender, receiver) = crossbeam_channel::unbounded();
        let mut state = MainLoopState::new(sender, Some(main.clone()));
        open_doc(&mut state, &main, main_on_disk);
        open_doc(&mut state, &c, c_on_disk);
        change_doc(&mut state, &main, 2, &main_unsaved);
        change_doc(&mut state, &c, 2, &c_unsaved);
        let published = drain_published(&receiver);
        let mut shown = sorted(shown_for(&published, &b, on_disk));
        assert_eq!(shown, saved, "{published:?}");

        for (path, text) in [(&c, &c_unsaved), (&main, &main_unsaved)] {
            change_doc(&mut state, path, 3, text);
            let published = drain_published(&receiver);
            shown = sorted(shown_for(&published, &b, shown));
            assert_eq!(
                shown,
                saved,
                "editing {} publishes b as check does: {published:?}",
                path.display()
            );
        }

        state.revalidate_open_documents();
        let published = drain_published(&receiver);
        let b_uri = crate::path_to_uri(&b).expect("file URI");
        let for_b = published
            .iter()
            .filter(|(u, _)| u.as_str() == b_uri.as_str()) // ratchet-allow: uri-string-eq comparing what was sent on the wire
            .map(|(_, codes)| sorted(codes.clone()));
        for codes in for_b {
            assert_eq!(codes, saved, "every publish of b agrees: {published:?}");
        }
    }

    /// Closing a buffer republishes the OTHER open ledger buffers too: b's
    /// buffer was validated against main's unsaved `open Assets:Q`, and once
    /// main is closed unsaved, b's own error is back without b being edited.
    #[test]
    fn closing_a_buffer_republishes_the_other_open_buffers() {
        let (_tmp, main, b) = ledger_dir(MAIN_ON_DISK);
        let (sender, receiver) = crossbeam_channel::unbounded();
        let mut state = MainLoopState::new(sender, Some(main.clone()));
        open_doc(&mut state, &main, MAIN_ON_DISK);
        open_doc(&mut state, &b, B_TEXT);
        change_doc(
            &mut state,
            &main,
            2,
            &format!("{MAIN_ON_DISK}2024-01-01 open Assets:Q\n"),
        );
        change_doc(&mut state, &b, 2, B_TEXT);
        let published = drain_published(&receiver);
        assert_eq!(
            last_published_for(&published, &b),
            Some(vec![]),
            "{published:?}"
        );

        close_doc(&mut state, &main);
        let published = drain_published(&receiver);
        assert_eq!(
            last_published_for(&published, &b),
            b_own(),
            "the open buffer b is republished without main's unsaved text: {published:?}"
        );
    }

    /// The clean view costs nothing extra: a pass for a clean buffer is ONE
    /// whole-ledger validation, other buffers open or not; only a broken
    /// buffer costs a second one, for its own view, whether or not it has a
    /// last clean parse.
    #[test]
    fn a_clean_pass_is_one_validation_and_a_broken_one_two() {
        let main_text = format!("include \"c.beancount\"\n{MAIN_ON_DISK}");
        let (_tmp, main, _b) = ledger_dir(&main_text);
        let c = main.with_file_name("c.beancount");
        std::fs::write(&c, "2024-01-01 open Assets:C\n").expect("write c");
        let (sender, receiver) = crossbeam_channel::unbounded();
        let mut state = MainLoopState::new(sender, Some(main.clone()));
        let runs =
            || crate::handlers::diagnostics::LEDGER_VALIDATION_RUNS.with(std::cell::Cell::get);

        let before = runs();
        open_doc(&mut state, &main, &main_text);
        open_doc(&mut state, &c, "2024-01-01 open Assets:C\n");
        change_doc(&mut state, &main, 2, &format!("{main_text}; edit\n"));
        assert_eq!(runs() - before, 3, "three clean passes");

        let before = runs();
        change_doc(&mut state, &main, 3, &format!("{main_text}garbage\n"));
        assert_eq!(runs() - before, 2, "broken with a last clean parse");

        let before = runs();
        open_doc(&mut state, &c, "garbage\n");
        assert_eq!(runs() - before, 2, "broken without one");
        drain_published(&receiver);
    }
}
