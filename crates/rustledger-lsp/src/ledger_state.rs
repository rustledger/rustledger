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

/// Discover the root journal file in a workspace directory.
///
/// Delegates to the loader so the LSP and `rledger format` agree on what a
/// root looks like; a file the two disagree about is a file that formats
/// differently on save than in a pre-commit hook.
pub fn discover_journal_file(workspace_root: &Path) -> Option<PathBuf> {
    let found = rustledger_loader::discover_journal_file(workspace_root);
    match &found {
        Some(p) => tracing::info!("Auto-discovered journal file: {}", p.display()),
        None => tracing::debug!(
            "No journal file found in workspace root: {}",
            workspace_root.display()
        ),
    }
    found
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

        // The LSP runs its own validation in `all_diagnostics` over the open-buffer
        // overlay and discards `ledger.errors`, so skip the loader's in-process
        // validation pass — otherwise (now that the `validation` feature is enabled
        // for the shared converter) every load/file-watch refresh would validate
        // the whole ledger twice. See diagnostics::all_diagnostics.
        let options = LoadOptions {
            validate: false,
            ..LoadOptions::default()
        };
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

    /// How numerals should be grouped when formatting `path`.
    ///
    /// Formatting honors the ledger's `render_commas` (and any per-commodity
    /// override) the same way `rledger format --ledger <root>` does — the
    /// options come from the journal ROOT, which is the only place they can
    /// come from, since the buffer being formatted is often an `include`d file
    /// with no options of its own.
    ///
    /// Returns the no-grouping default in the two cases where those options
    /// cannot be said to apply:
    ///
    /// - no ledger is loaded (startup race, or the load failed) — formatting
    ///   must still work, so it falls back rather than blocking;
    /// - the buffer is not part of the loaded ledger. Editing a stray
    ///   `.beancount` file that no journal includes must not pick up an
    ///   unrelated ledger's display policy.
    pub fn grouping_style_for(&self, path: &Path) -> rustledger_parser::format::GroupingStyle<'_> {
        match &self.ledger {
            Some(ledger) if self.contains_file(path) => {
                rustledger_parser::format::GroupingStyle::from_context(&ledger.display_context)
            }
            _ => rustledger_parser::format::GroupingStyle::default(),
        }
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

#[cfg(test)]
mod grouping_style_tests {
    use super::*;
    use std::io::Write;

    /// Writes a two-file ledger whose ROOT declares `render_commas`, plus an
    /// unrelated file no journal includes. Returns (dir, root, included,
    /// outsider).
    fn ledger_with_grouping() -> (tempfile::TempDir, PathBuf, PathBuf, PathBuf) {
        let dir = tempfile::tempdir().expect("tempdir");
        let root = dir.path().join("main.beancount");
        let included = dir.path().join("postings.beancount");
        let outsider = dir.path().join("scratch.beancount");

        let mut f = std::fs::File::create(&root).expect("create root");
        writeln!(f, "option \"render_commas\" \"TRUE\"").unwrap();
        writeln!(f, "include \"postings.beancount\"").unwrap();
        writeln!(f, "2020-01-01 open Assets:Local").unwrap();
        writeln!(f, "2020-01-01 open Equity:Opening").unwrap();

        let mut f = std::fs::File::create(&included).expect("create include");
        writeln!(f, "2020-01-02 * \"x\"").unwrap();
        writeln!(f, "  Assets:Local     1234567.89 IQD").unwrap();
        writeln!(f, "  Equity:Opening").unwrap();

        std::fs::write(&outsider, "2020-01-01 open Assets:Other\n").expect("create outsider");
        (dir, root, included, outsider)
    }

    /// The journal ROOT's options govern formatting of an INCLUDED buffer.
    ///
    /// This is the whole point of the gate: the file the user is editing
    /// usually has no `option` lines of its own, exactly like the CLI's
    /// `rledger format --ledger <root> <included-file>`.
    #[test]
    fn an_included_buffer_inherits_the_roots_grouping() {
        let (_dir, root, included, _outsider) = ledger_with_grouping();
        let mut state = LedgerState::new();
        state.load(&root).expect("load");

        assert!(
            state.grouping_style_for(&root).groups_anything(),
            "the root declared render_commas"
        );
        assert!(
            state.grouping_style_for(&included).groups_anything(),
            "an included file has no options of its own and must inherit the root's"
        );
    }

    /// A buffer outside the loaded ledger must NOT pick up its display policy,
    /// and neither must anything before a ledger has loaded.
    #[test]
    fn a_buffer_outside_the_ledger_does_not_group() {
        let (_dir, root, _included, outsider) = ledger_with_grouping();

        let fresh = LedgerState::new();
        assert!(
            !fresh.grouping_style_for(&root).groups_anything(),
            "no ledger loaded yet (startup race, or load failed): formatting \
             must still work, ungrouped"
        );

        let mut state = LedgerState::new();
        state.load(&root).expect("load");
        assert!(
            !state.grouping_style_for(&outsider).groups_anything(),
            "a stray file no journal includes must not inherit an unrelated \
             ledger's grouping"
        );
    }

    /// A ledger that declares nothing groups nothing — the overwhelmingly
    /// common case, and the one that keeps the cached-alignment fast path.
    #[test]
    fn a_ledger_without_the_option_does_not_group() {
        let dir = tempfile::tempdir().expect("tempdir");
        let root = dir.path().join("main.beancount");
        std::fs::write(&root, "2020-01-01 open Assets:Local\n").expect("write");

        let mut state = LedgerState::new();
        state.load(&root).expect("load");
        assert!(!state.grouping_style_for(&root).groups_anything());
    }
}
