//! Ledger state management for multi-file support.
//!
//! This module provides the [`LedgerState`] which loads and maintains
//! the full ledger state from a root journal file and all its includes.

use parking_lot::RwLock;
use rustledger_core::{Directive, PriceAnnotation};
use rustledger_loader::{Ledger, LoadOptions, load};
use rustledger_parser::Spanned;
use std::collections::{HashMap, HashSet};
use std::path::{Path, PathBuf};
use std::sync::Arc;

/// Common root journal filenames to check, in priority order.
const COMMON_ROOT_NAMES: &[&str] = &[
    "main.bean",
    "main.beancount",
    "ledger.bean",
    "ledger.beancount",
    "journal.bean",
    "journal.beancount",
    "index.bean",
    "index.beancount",
];

/// Discover the root journal file in a workspace directory.
///
/// Checks for common root filenames in the workspace root directory.
/// Returns the first one found that exists.
pub fn discover_journal_file(workspace_root: &Path) -> Option<PathBuf> {
    for name in COMMON_ROOT_NAMES {
        let candidate = workspace_root.join(name);
        if candidate.exists() && candidate.is_file() {
            tracing::info!("Auto-discovered journal file: {}", candidate.display());
            return Some(candidate);
        }
    }
    tracing::debug!(
        "No journal file found in workspace root: {}",
        workspace_root.display()
    );
    None
}

/// Extract currency from a price annotation if available. `kind`
/// (Unit vs Total) doesn't change the currency; we just walk the
/// underlying amount.
fn extract_price_currency(price: &PriceAnnotation) -> Option<String> {
    price
        .amount
        .as_ref()
        .and_then(|inc| inc.currency())
        .map(str::to_string)
}

/// Configuration for the LSP server, parsed from initialization options.
#[derive(Debug, Clone, Default)]
pub struct LspConfig {
    /// Path to the root journal file (e.g., "main.bean").
    /// When set, the LSP loads this file and all its includes for
    /// complete diagnostics and completions across the entire ledger.
    pub journal_file: Option<PathBuf>,
}

impl LspConfig {
    /// Parse configuration from LSP initialization options.
    pub fn from_init_options(options: Option<&serde_json::Value>) -> Self {
        let mut config = Self::default();

        if let Some(opts) = options {
            // Support both camelCase and snake_case
            if let Some(path) = opts
                .get("journalFile")
                .or_else(|| opts.get("journal_file"))
                .and_then(|v| v.as_str())
            {
                config.journal_file = Some(PathBuf::from(path));
            }
        }

        config
    }
}

/// Holds the loaded ledger state from the root journal file.
///
/// This is used to provide cross-file completions, diagnostics, and navigation.
pub struct LedgerState {
    /// The loaded ledger (if a journal file is configured).
    ledger: Option<Ledger>,
    /// All files that are part of this ledger (main + includes).
    included_files: HashSet<PathBuf>,
    /// Accounts extracted from the full ledger.
    accounts: Vec<String>,
    /// Currencies extracted from the full ledger.
    currencies: Vec<String>,
    /// Payees extracted from the full ledger.
    payees: Vec<String>,
    /// Tags extracted from the full ledger (without the `#` sigil).
    tags: Vec<String>,
    /// Links extracted from the full ledger (without the `^` sigil).
    links: Vec<String>,
    /// Account to file mapping for go-to-definition.
    account_locations: HashMap<String, (PathBuf, u32)>,
}

impl Default for LedgerState {
    fn default() -> Self {
        Self::new()
    }
}

impl LedgerState {
    /// Create a new empty ledger state.
    pub fn new() -> Self {
        Self {
            ledger: None,
            included_files: HashSet::new(),
            accounts: Vec::new(),
            currencies: Vec::new(),
            payees: Vec::new(),
            tags: Vec::new(),
            links: Vec::new(),
            account_locations: HashMap::new(),
        }
    }

    /// Load the ledger from a journal file.
    ///
    /// Returns the set of files that were loaded (for file watching).
    pub fn load(&mut self, journal_path: &Path) -> Result<HashSet<PathBuf>, String> {
        tracing::info!("Loading journal file: {}", journal_path.display());

        let options = LoadOptions::default();
        match load(journal_path, &options) {
            Ok(ledger) => {
                // Extract included files from source map. Canonicalize
                // each path at insert time so the symmetric lookup in
                // `contains_file` matches editor-supplied URIs whose
                // canonical form may differ (symlinks, `./` segments,
                // relative includes). Fallback to the raw path when
                // canonicalize fails (file was deleted between load
                // and here, or the loader returned a synthetic path);
                // those entries can't be matched by an editor URI
                // anyway.
                self.included_files.clear();
                for file in ledger.source_map.files() {
                    let canonical = file
                        .path
                        .canonicalize()
                        .unwrap_or_else(|_| file.path.clone());
                    self.included_files.insert(canonical);
                }

                // Extract accounts, currencies, payees for completions
                self.extract_completion_data(&ledger.directives);

                // Extract account locations for go-to-definition
                self.extract_account_locations(&ledger);

                let files = self.included_files.clone();
                self.ledger = Some(ledger);

                tracing::info!(
                    "Loaded {} files, {} accounts, {} currencies",
                    self.included_files.len(),
                    self.accounts.len(),
                    self.currencies.len()
                );

                Ok(files)
            }
            Err(e) => {
                tracing::error!("Failed to load journal: {e}");
                Err(e.to_string())
            }
        }
    }

    /// Check if a file is part of this ledger.
    ///
    /// Canonicalizes `path` before lookup so editor-supplied URIs
    /// (which may carry `./`, `..`, or symlink path segments) match
    /// the canonical paths inserted at load time. A canonicalize
    /// failure (broken symlink, file just deleted) means the file is
    /// not on disk in any form addressable by the loaded ledger, so
    /// the answer is `false`. One stat() per call; the lookup runs
    /// on the codeLens hot path, but the cost is per-request (not
    /// per-included-file as iterating included_files would be).
    pub fn contains_file(&self, path: &Path) -> bool {
        match path.canonicalize() {
            Ok(canonical) => self.included_files.contains(&canonical),
            Err(_) => self.included_files.contains(path),
        }
    }

    /// Get all accounts from the full ledger.
    pub fn accounts(&self) -> &[String] {
        &self.accounts
    }

    /// Get all currencies from the full ledger.
    pub fn currencies(&self) -> &[String] {
        &self.currencies
    }

    /// Get all payees from the full ledger.
    pub fn payees(&self) -> &[String] {
        &self.payees
    }

    /// Get all tags from the full ledger (without the `#` sigil).
    pub fn tags(&self) -> &[String] {
        &self.tags
    }

    /// Get all links from the full ledger (without the `^` sigil).
    pub fn links(&self) -> &[String] {
        &self.links
    }

    /// Get all directives from the full ledger.
    pub fn directives(&self) -> Option<&[Spanned<Directive>]> {
        self.ledger.as_ref().map(|l| l.directives.as_slice())
    }

    /// Get the loaded ledger.
    pub fn ledger(&self) -> Option<&Ledger> {
        self.ledger.as_ref()
    }

    /// Get all included files.
    pub fn included_files(&self) -> &HashSet<PathBuf> {
        &self.included_files
    }

    /// Find where an account is defined.
    pub fn find_account_definition(&self, account: &str) -> Option<(PathBuf, u32)> {
        self.account_locations.get(account).cloned()
    }

    /// Extract completion data from directives.
    fn extract_completion_data(&mut self, directives: &[Spanned<Directive>]) {
        self.accounts.clear();
        self.currencies.clear();
        self.payees.clear();
        self.tags.clear();
        self.links.clear();

        let mut accounts_set: HashSet<String> = HashSet::new();
        let mut currencies_set: HashSet<String> = HashSet::new();
        let mut payees_set: HashSet<String> = HashSet::new();

        for spanned in directives {
            match &spanned.value {
                Directive::Open(open) => {
                    accounts_set.insert(open.account.to_string());
                    for currency in &open.currencies {
                        currencies_set.insert(currency.to_string());
                    }
                }
                Directive::Close(close) => {
                    accounts_set.insert(close.account.to_string());
                }
                Directive::Balance(balance) => {
                    accounts_set.insert(balance.account.to_string());
                    currencies_set.insert(balance.amount.currency.to_string());
                }
                Directive::Pad(pad) => {
                    accounts_set.insert(pad.account.to_string());
                    accounts_set.insert(pad.source_account.to_string());
                }
                Directive::Transaction(txn) => {
                    if let Some(payee) = &txn.payee {
                        payees_set.insert(payee.to_string());
                    }
                    for posting in &txn.postings {
                        accounts_set.insert(posting.account.to_string());
                        if let Some(units) = &posting.units
                            && let Some(currency) = units.currency()
                        {
                            currencies_set.insert(currency.to_string());
                        }
                        if let Some(cost) = &posting.cost
                            && let Some(currency) = &cost.currency
                        {
                            currencies_set.insert(currency.to_string());
                        }
                        // Extract currency from price annotation
                        if let Some(price) = &posting.price
                            && let Some(currency) = extract_price_currency(price)
                        {
                            currencies_set.insert(currency);
                        }
                    }
                }
                Directive::Commodity(commodity) => {
                    currencies_set.insert(commodity.currency.to_string());
                }
                Directive::Document(doc) => {
                    accounts_set.insert(doc.account.to_string());
                }
                Directive::Note(note) => {
                    accounts_set.insert(note.account.to_string());
                }
                _ => {}
            }
        }

        self.accounts = accounts_set.into_iter().collect();
        self.accounts.sort();
        self.currencies = currencies_set.into_iter().collect();
        self.currencies.sort();
        self.payees = payees_set.into_iter().collect();
        self.payees.sort();

        // Tags and links delegate to the core visitor (the canonical
        // enumeration point) rather than a hand-rolled walk, so the
        // ledger sees tags/links in every position they can occur
        // (transaction/document fields, metadata, Custom values), and
        // stays in lockstep with the LSP's per-file extraction.
        self.tags = rustledger_core::extract_tags_iter(directives.iter().map(|s| &s.value));
        self.links = rustledger_core::extract_links_iter(directives.iter().map(|s| &s.value));
    }

    /// Extract account definition locations from the ledger.
    fn extract_account_locations(&mut self, ledger: &Ledger) {
        self.account_locations.clear();

        for spanned in &ledger.directives {
            if let Directive::Open(open) = &spanned.value {
                // Use file_id from the spanned directive to get the correct source file
                if let Some(file) = ledger.source_map.get(spanned.file_id as usize) {
                    let (line, _col) = file.line_col(spanned.span.start);
                    self.account_locations
                        .insert(open.account.to_string(), (file.path.clone(), line as u32));
                }
            }
        }
    }
}

/// Thread-safe wrapper for ledger state.
pub type SharedLedgerState = Arc<RwLock<LedgerState>>;

/// Create a new shared ledger state.
pub fn new_shared_ledger_state() -> SharedLedgerState {
    Arc::new(RwLock::new(LedgerState::new()))
}
