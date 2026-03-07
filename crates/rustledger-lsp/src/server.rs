//! Main LSP server implementation.

use crate::handlers::execute_command::COMMANDS;
use crate::handlers::on_type_formatting::{FIRST_TRIGGER_CHARACTER, MORE_TRIGGER_CHARACTERS};
use crate::handlers::semantic_tokens::get_capabilities as get_semantic_tokens_capabilities;
use crate::handlers::signature_help::TRIGGER_CHARACTERS as SIGNATURE_TRIGGER_CHARACTERS;
use crate::ledger_state::{LspConfig, discover_journal_file};
use crate::main_loop::run_main_loop;
use crate::uri_to_path;
use lsp_server::Connection;
use lsp_types::InitializeParams;

/// The LSP server.
pub struct Server {
    /// Connection to the LSP client.
    connection: Connection,
    /// Initialize parameters from client.
    init_params: InitializeParams,
    /// LSP configuration parsed from init options.
    config: LspConfig,
}

impl Server {
    /// Create a new LSP server from a connection.
    pub fn new(connection: Connection, init_params: InitializeParams) -> Self {
        // Parse configuration from initialization options
        let config = LspConfig::from_init_options(init_params.initialization_options.as_ref());

        if let Some(ref journal) = config.journal_file {
            tracing::info!("Journal file configured: {}", journal.display());
        }

        Self {
            connection,
            init_params,
            config,
        }
    }

    /// Run the server's main loop.
    pub fn run(self) {
        tracing::info!("Starting Beancount Language Server v{}", crate::VERSION);

        // Resolve journal file path relative to workspace root if needed
        let journal_file = self.resolve_journal_path();

        if let Some(ref path) = journal_file {
            tracing::info!("Using journal file: {}", path.display());
        }

        if let Some(folders) = &self.init_params.workspace_folders
            && let Some(folder) = folders.first()
        {
            tracing::info!("Workspace root: {}", folder.uri.as_str());
        }

        // Run the main event loop with the journal file configuration
        let (sender, receiver) = (self.connection.sender, self.connection.receiver);
        run_main_loop(receiver, sender, journal_file);

        tracing::info!("Server shutdown complete");
    }

    /// Resolve the journal file path, making it absolute if necessary.
    /// If no explicit journal file is configured, attempts auto-discovery.
    fn resolve_journal_path(&self) -> Option<std::path::PathBuf> {
        // Get workspace root path for resolution and discovery
        let workspace_root = self.get_workspace_root();

        // If explicit config provided, resolve it
        if let Some(journal) = &self.config.journal_file {
            return self.resolve_explicit_journal(journal, workspace_root.as_deref());
        }

        // No explicit config - try auto-discovery in workspace root
        if let Some(root) = workspace_root
            && let Some(discovered) = discover_journal_file(&root)
        {
            return Some(discovered);
        }

        // Also try current directory as fallback for discovery
        if let Ok(cwd) = std::env::current_dir()
            && let Some(discovered) = discover_journal_file(&cwd)
        {
            return Some(discovered);
        }

        tracing::debug!("No journal file configured or discovered");
        None
    }

    /// Get the workspace root path from init params.
    fn get_workspace_root(&self) -> Option<std::path::PathBuf> {
        self.init_params
            .workspace_folders
            .as_ref()
            .and_then(|folders| folders.first())
            .and_then(|folder| uri_to_path(&folder.uri))
    }

    /// Resolve an explicitly configured journal path.
    fn resolve_explicit_journal(
        &self,
        journal: &std::path::Path,
        workspace_root: Option<&std::path::Path>,
    ) -> Option<std::path::PathBuf> {
        // If already absolute, use as-is
        if journal.is_absolute() {
            return Some(journal.to_path_buf());
        }

        // Try to resolve relative to workspace root
        if let Some(root) = workspace_root {
            let resolved = root.join(journal);
            if resolved.exists() {
                return Some(resolved);
            }
        }

        // Fall back to current directory
        let resolved = std::env::current_dir()
            .ok()
            .map(|cwd| cwd.join(journal))
            .filter(|p| p.exists());

        if resolved.is_none() {
            tracing::warn!(
                "Journal file '{}' not found relative to workspace or current directory",
                journal.display()
            );
        }

        resolved
    }
}

/// Start the LSP server using stdio transport.
pub fn start_stdio() -> Result<(), Box<dyn std::error::Error + Send + Sync>> {
    tracing::info!("Starting LSP server on stdio");

    // Create connection using stdio
    let (connection, io_threads) = Connection::stdio();

    // Wait for initialize request
    let (id, params) = connection.initialize_start()?;
    let init_params: InitializeParams = serde_json::from_value(params)?;

    // Build server capabilities
    let capabilities = lsp_types::ServerCapabilities {
        text_document_sync: Some(lsp_types::TextDocumentSyncCapability::Kind(
            lsp_types::TextDocumentSyncKind::FULL,
        )),
        completion_provider: Some(lsp_types::CompletionOptions {
            trigger_characters: Some(vec![
                ":".to_string(),  // Account segments
                " ".to_string(),  // After keywords
                "\"".to_string(), // Strings (payees, narrations)
            ]),
            resolve_provider: Some(true), // Enable completion resolve for detailed info
            ..Default::default()
        }),
        definition_provider: Some(lsp_types::OneOf::Left(true)),
        references_provider: Some(lsp_types::OneOf::Left(true)),
        hover_provider: Some(lsp_types::HoverProviderCapability::Simple(true)),
        document_symbol_provider: Some(lsp_types::OneOf::Left(true)),
        semantic_tokens_provider: Some(get_semantic_tokens_capabilities()),
        code_action_provider: Some(lsp_types::CodeActionProviderCapability::Options(
            lsp_types::CodeActionOptions {
                code_action_kinds: Some(vec![
                    lsp_types::CodeActionKind::QUICKFIX,
                    lsp_types::CodeActionKind::REFACTOR,
                ]),
                resolve_provider: Some(true), // Enable resolve for lazy-loading edits
                work_done_progress_options: Default::default(),
            },
        )),
        workspace_symbol_provider: Some(lsp_types::OneOf::Left(true)),
        rename_provider: Some(lsp_types::OneOf::Right(lsp_types::RenameOptions {
            prepare_provider: Some(true),
            work_done_progress_options: Default::default(),
        })),
        document_formatting_provider: Some(lsp_types::OneOf::Left(true)),
        document_range_formatting_provider: Some(lsp_types::OneOf::Left(true)),
        document_link_provider: Some(lsp_types::DocumentLinkOptions {
            resolve_provider: Some(true), // Enable resolve to verify file existence
            work_done_progress_options: Default::default(),
        }),
        inlay_hint_provider: Some(lsp_types::OneOf::Right(
            lsp_types::InlayHintServerCapabilities::Options(lsp_types::InlayHintOptions {
                resolve_provider: Some(true), // Enable resolve for rich tooltips
                work_done_progress_options: Default::default(),
            }),
        )),
        selection_range_provider: Some(lsp_types::SelectionRangeProviderCapability::Simple(true)),
        folding_range_provider: Some(lsp_types::FoldingRangeProviderCapability::Simple(true)),
        document_highlight_provider: Some(lsp_types::OneOf::Left(true)),
        linked_editing_range_provider: Some(
            lsp_types::LinkedEditingRangeServerCapabilities::Simple(true),
        ),
        document_on_type_formatting_provider: Some(lsp_types::DocumentOnTypeFormattingOptions {
            first_trigger_character: FIRST_TRIGGER_CHARACTER.to_string(),
            more_trigger_character: Some(
                MORE_TRIGGER_CHARACTERS
                    .iter()
                    .map(|s| s.to_string())
                    .collect(),
            ),
        }),
        code_lens_provider: Some(lsp_types::CodeLensOptions {
            resolve_provider: Some(true), // Enable resolve for lazy-loading balance verification
        }),
        color_provider: Some(lsp_types::ColorProviderCapability::Simple(true)),
        declaration_provider: Some(lsp_types::DeclarationCapability::Simple(true)),
        call_hierarchy_provider: Some(lsp_types::CallHierarchyServerCapability::Simple(true)),
        signature_help_provider: Some(lsp_types::SignatureHelpOptions {
            trigger_characters: Some(
                SIGNATURE_TRIGGER_CHARACTERS
                    .iter()
                    .map(|s| s.to_string())
                    .collect(),
            ),
            retrigger_characters: None,
            work_done_progress_options: Default::default(),
        }),
        execute_command_provider: Some(lsp_types::ExecuteCommandOptions {
            commands: COMMANDS.iter().map(|s| s.to_string()).collect(),
            work_done_progress_options: Default::default(),
        }),
        // Type hierarchy: advertised via experimental until lsp-types adds native support
        experimental: Some(serde_json::json!({
            "typeHierarchyProvider": true
        })),
        // Workspace capabilities
        workspace: Some(lsp_types::WorkspaceServerCapabilities {
            workspace_folders: Some(lsp_types::WorkspaceFoldersServerCapabilities {
                supported: Some(true),
                change_notifications: Some(lsp_types::OneOf::Left(true)),
            }),
            file_operations: None, // File operations (create/rename/delete) not needed for Beancount
        }),
        ..Default::default()
    };

    let server_info = lsp_types::ServerInfo {
        name: "rledger-lsp".to_string(),
        version: Some(crate::VERSION.to_string()),
    };

    let init_result = lsp_types::InitializeResult {
        capabilities,
        server_info: Some(server_info),
    };

    // Complete initialization handshake
    connection.initialize_finish(id, serde_json::to_value(init_result)?)?;

    tracing::info!("LSP initialized successfully");

    // Create and run server
    let server = Server::new(connection, init_params);
    server.run();

    // Wait for IO threads to finish
    io_threads.join()?;

    Ok(())
}
