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
use crate::handlers::diagnostics::parse_errors_to_diagnostics;
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
use crate::snapshot::bump_revision;
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
    CompletionItem, CompletionParams, DiagnosticOptions, DiagnosticServerCapabilities,
    DocumentColorParams, DocumentFormattingParams, DocumentHighlightParams, DocumentLink,
    DocumentLinkParams, DocumentOnTypeFormattingParams, DocumentRangeFormattingParams,
    DocumentSymbolParams, ExecuteCommandParams, FoldingRangeParams, GotoDefinitionParams,
    HoverParams, InitializeParams, InitializeResult, InlayHint, InlayHintParams,
    LinkedEditingRangeParams, PublishDiagnosticsParams, ReferenceParams, RenameParams,
    SelectionRangeParams, SemanticTokensDeltaParams, SemanticTokensParams,
    SemanticTokensRangeParams, ServerCapabilities, ServerInfo, SignatureHelpParams,
    TextDocumentPositionParams, TextDocumentSyncCapability, TextDocumentSyncKind,
    TypeHierarchyPrepareParams, TypeHierarchySubtypesParams, TypeHierarchySupertypesParams, Uri,
    WorkspaceSymbolParams,
};
use parking_lot::RwLock;
use rustledger_parser::{ParseResult, parse};
use std::collections::HashMap;
use std::path::PathBuf;
use std::sync::Arc;

/// Events processed by the main loop.
#[derive(Debug)]
pub enum Event {
    /// LSP message from the client.
    Message(Message),
    /// Response from a background task.
    #[allow(dead_code)] // Will be used when we add threadpool
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
#[allow(dead_code)] // Will be used when we add threadpool
pub struct TaskResult {
    /// The request ID this task is responding to.
    pub request_id: lsp_server::RequestId,
    /// The result of the task, or an error message.
    pub result: Result<serde_json::Value, String>,
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
    /// Full ledger state (loaded from journal file if configured).
    pub ledger_state: SharedLedgerState,
    /// Path to the journal file (if configured).
    pub journal_file: Option<PathBuf>,
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

        Self {
            vfs: Arc::new(RwLock::new(Vfs::new())),
            sender,
            diagnostics: HashMap::new(),
            shutdown_requested: false,
            ledger_state,
            journal_file,
        }
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
            Event::Task(_result) => {
                // TODO: Send response back to client
            }
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
    fn handle_request(&mut self, req: lsp_server::Request) {
        let id = req.id.clone();

        // Dispatch based on method
        let result = match req.method.as_str() {
            Initialize::METHOD => self.handle_initialize(req),
            Shutdown::METHOD => {
                self.shutdown_requested = true;
                Ok(serde_json::Value::Null)
            }
            Completion::METHOD => self.handle_completion_request(req),
            GotoDefinition::METHOD => self.handle_goto_definition_request(req),
            References::METHOD => self.handle_references_request(req),
            HoverRequest::METHOD => self.handle_hover_request(req),
            DocumentSymbolRequest::METHOD => self.handle_document_symbols_request(req),
            SemanticTokensFullRequest::METHOD => self.handle_semantic_tokens_request(req),
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
            CodeLensResolve::METHOD => self.handle_code_lens_resolve_request(req),
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
                tracing::warn!("Unhandled request: {}", req.method);
                Err(format!("Unhandled request: {}", req.method))
            }
        };

        // Send response
        let response = match result {
            Ok(value) => lsp_server::Response::new_ok(id, value),
            Err(msg) => {
                // Use MethodNotFound only for truly unknown methods,
                // InternalError for handler failures
                let error_code = if msg.starts_with("Unhandled request") {
                    lsp_server::ErrorCode::MethodNotFound
                } else {
                    lsp_server::ErrorCode::InternalError
                };
                lsp_server::Response::new_err(id, error_code as i32, msg)
            }
        };

        self.send(lsp_server::Message::Response(response));
    }

    /// Handle the initialize request.
    fn handle_initialize(&mut self, req: lsp_server::Request) -> Result<serde_json::Value, String> {
        let _params: InitializeParams =
            serde_json::from_value(req.params).map_err(|e| e.to_string())?;

        let capabilities = ServerCapabilities {
            text_document_sync: Some(TextDocumentSyncCapability::Kind(TextDocumentSyncKind::FULL)),
            diagnostic_provider: Some(DiagnosticServerCapabilities::Options(DiagnosticOptions {
                ..Default::default()
            })),
            ..Default::default()
        };

        let result = InitializeResult {
            capabilities,
            server_info: Some(ServerInfo {
                name: "rledger-lsp".to_string(),
                version: Some(crate::VERSION.to_string()),
            }),
        };

        serde_json::to_value(result).map_err(|e| e.to_string())
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

        let response = handle_completion(&params, &text, &parse_result, ledger_state);

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

        let response = handle_goto_definition(&params, &text, &parse_result, uri);

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

        let response = handle_references(&params, &text, &parse_result, uri);

        serde_json::to_value(response).map_err(|e| e.to_string())
    }

    /// Handle the textDocument/hover request.
    fn handle_hover_request(&self, req: lsp_server::Request) -> Result<serde_json::Value, String> {
        let params: HoverParams = serde_json::from_value(req.params).map_err(|e| e.to_string())?;

        let uri = &params.text_document_position_params.text_document.uri;
        let (text, parse_result) = self.get_document_data(uri);

        let response = handle_hover(&params, &text, &parse_result);

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

        let response = handle_document_symbols(&params, &text, &parse_result);

        serde_json::to_value(response).map_err(|e| e.to_string())
    }

    /// Handle the textDocument/semanticTokens/full request.
    fn handle_semantic_tokens_request(
        &self,
        req: lsp_server::Request,
    ) -> Result<serde_json::Value, String> {
        let params: SemanticTokensParams =
            serde_json::from_value(req.params).map_err(|e| e.to_string())?;

        let uri = &params.text_document.uri;
        let (text, parse_result) = self.get_document_data(uri);

        let response = handle_semantic_tokens(&params, &text, &parse_result);

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
        let response = handle_semantic_tokens_delta(&params, &text, &parse_result, None);

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

        let response = handle_semantic_tokens_range(&params, &text, &parse_result);

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

        let response = handle_code_actions(&params, &text, &parse_result);

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

        let resolved = handle_code_action_resolve(action, &text, &parse_result, &uri);

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

        let response = handle_workspace_symbols(&params, &documents);

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

        let response = handle_prepare_rename(&params, &text, &parse_result);

        serde_json::to_value(response).map_err(|e| e.to_string())
    }

    /// Handle the textDocument/rename request.
    fn handle_rename_request(&self, req: lsp_server::Request) -> Result<serde_json::Value, String> {
        let params: RenameParams = serde_json::from_value(req.params).map_err(|e| e.to_string())?;

        let uri = &params.text_document_position.text_document.uri;
        let (text, parse_result) = self.get_document_data(uri);

        let response = handle_rename(&params, &text, &parse_result);

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

        let response = handle_formatting(&params, &text, &parse_result);

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

        let response = handle_folding_ranges(&params, &text, &parse_result);

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

        let response = handle_range_formatting(&params, &text, &parse_result);

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

        let response = handle_document_links(&params, &text, &parse_result);

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

        let response = handle_inlay_hints(&params, &text, &parse_result);

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

        let response = handle_selection_range(&params, &text, &parse_result);

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

        let response = handle_prepare_type_hierarchy(&params, &text, &parse_result, uri);

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

        let response = handle_supertypes(&params, &text, &parse_result, uri);

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

        let response = handle_subtypes(&params, &text, &parse_result, uri);

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

        let response = handle_document_highlight(&params, &text, &parse_result);

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

        let response = handle_linked_editing_range(&params, &text, &parse_result);

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

        let response = handle_on_type_formatting(&params, &text);

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

        let response = handle_code_lens(&params, &text, &parse_result);

        serde_json::to_value(response).map_err(|e| e.to_string())
    }

    /// Handle the codeLens/resolve request.
    fn handle_code_lens_resolve_request(
        &self,
        req: lsp_server::Request,
    ) -> Result<serde_json::Value, String> {
        let lens: CodeLens = serde_json::from_value(req.params).map_err(|e| e.to_string())?;

        // Get the document URI from the lens's data field
        let uri: Uri = if let Some(data) = &lens.data {
            data.get("uri")
                .and_then(|v| v.as_str())
                .and_then(|s| s.parse().ok())
                .unwrap_or_else(|| "file:///unknown".parse().unwrap())
        } else {
            "file:///unknown".parse().unwrap()
        };

        let (_text, parse_result) = self.get_document_data(&uri);
        let resolved = handle_code_lens_resolve(lens, &parse_result);

        serde_json::to_value(resolved).map_err(|e| e.to_string())
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

        let response = handle_document_color(&params, &text, &parse_result);

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

        // Handle go-to-declaration (same as definition for Beancount)
        let response = handle_goto_declaration(&params, &text, &parse_result, uri);

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

        let response = handle_prepare_call_hierarchy(&params, &text, &parse_result, uri);

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

        let response = handle_incoming_calls(&params, &text, &parse_result, uri);

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

        let response = handle_outgoing_calls(&params, &text, &parse_result, uri);

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
        let response = handle_signature_help(&params, &text);

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
            let response = handle_execute_command(&params, &text, &parse_result, &uri);
            return Ok(response.unwrap_or(serde_json::Value::Null));
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
        let response = handle_execute_command(&params, &text, &parse_result, &uri);

        Ok(response.unwrap_or(serde_json::Value::Null))
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
        let resolved = handle_completion_resolve(item, &parse_result);

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
                std::process::exit(if self.shutdown_requested { 0 } else { 1 });
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
        bump_revision();

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
            bump_revision();

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

    /// Parse document and publish diagnostics.
    fn publish_diagnostics(&mut self, uri: &Uri, text: &str) {
        // Parse the document
        let result = parse(text);

        // Convert errors to LSP diagnostics
        let diagnostics = parse_errors_to_diagnostics(&result, text);

        tracing::debug!(
            "Publishing {} diagnostics for {}",
            diagnostics.len(),
            uri.as_str()
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
/// # Arguments
/// * `receiver` - Channel to receive LSP messages from the client
/// * `sender` - Channel to send LSP messages to the client
/// * `journal_file` - Optional path to the root journal file for multi-file support
pub fn run_main_loop(
    receiver: Receiver<lsp_server::Message>,
    sender: Sender<lsp_server::Message>,
    journal_file: Option<PathBuf>,
) {
    let mut state = MainLoopState::new(sender, journal_file);

    tracing::info!("Main loop started");

    for msg in receiver {
        let event = match msg {
            lsp_server::Message::Request(req) => Event::Message(Message::Request(req)),
            lsp_server::Message::Notification(notif) => {
                Event::Message(Message::Notification(notif))
            }
            lsp_server::Message::Response(resp) => Event::Message(Message::Response(resp)),
        };

        state.handle_event(event);
    }

    tracing::info!("Main loop ended");
}
