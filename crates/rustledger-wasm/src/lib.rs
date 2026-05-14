//! Beancount WASM Bindings.
//!
//! This crate provides WebAssembly bindings for using Beancount from JavaScript/TypeScript.
//!
//! # Features
//!
//! - Parse Beancount files (single and multi-file with includes)
//! - Validate ledgers
//! - Run BQL queries
//! - Format directives
//! - [`ParsedLedger`] — cached single-file with editor features (completions, hover, etc.)
//! - [`Ledger`] — cached multi-file with queries and cross-file completions
//!
//! # Example (JavaScript)
//!
//! ```javascript
//! import init, { parse, validateSource, query } from '@rustledger/wasm';
//!
//! await init();
//!
//! const source = `
//! 2024-01-01 open Assets:Bank USD
//! 2024-01-15 * "Coffee"
//!   Expenses:Food  5.00 USD
//!   Assets:Bank   -5.00 USD
//! `;
//!
//! const result = parse(source);
//! if (result.errors.length === 0) {
//!     const validation = validateSource(source);
//!     console.log('Validation errors:', validation.errors);
//! }
//! ```

#![forbid(unsafe_code)]
#![warn(missing_docs)]
// wasm_bindgen doesn't support const fn on exported methods
#![allow(clippy::missing_const_for_fn)]

// Internal modules
mod cache;
mod convert;
mod editor;
mod helpers;
mod utils;

// Public modules
pub mod types;

// Public API modules
mod api;
mod parsed_ledger;

// Re-export public API
pub use api::{balances, format, parse, query, validate_source, version};
pub use api::{hash_sources, parse_multi_file, query_multi_file, validate_multi_file};

#[cfg(feature = "completions")]
pub use api::bql_completions;

#[cfg(feature = "plugins")]
pub use api::{list_plugins, run_plugin};

pub use api::expand_pads;
pub use parsed_ledger::{Ledger, ParsedLedger};

use wasm_bindgen::prelude::*;

// =============================================================================
// TypeScript Type Definitions
// =============================================================================

#[wasm_bindgen(typescript_custom_section)]
const TS_TYPES: &'static str = r#"
/** Error severity level. */
export type Severity = 'error' | 'warning';

/** Error with source location information. */
export interface BeancountError {
    message: string;
    line?: number;
    column?: number;
    severity: Severity;
}

/** Amount with number and currency. */
export interface Amount {
    number: string;
    currency: string;
}

/** Posting cost specification. */
export interface PostingCost {
    number_per?: string;
    currency?: string;
    date?: string;
    label?: string;
}

/** A posting within a transaction. */
export interface Posting {
    account: string;
    units?: Amount;
    cost?: PostingCost;
    price?: Amount;
}

/** Base directive with date. */
interface BaseDirective {
    date: string;
}

/** Transaction directive. */
export interface TransactionDirective extends BaseDirective {
    type: 'transaction';
    flag: string;
    payee?: string;
    narration?: string;
    tags: string[];
    links: string[];
    postings: Posting[];
}

/** Balance assertion directive. */
export interface BalanceDirective extends BaseDirective {
    type: 'balance';
    account: string;
    amount: Amount;
}

/** Open account directive. */
export interface OpenDirective extends BaseDirective {
    type: 'open';
    account: string;
    currencies: string[];
    booking?: string;
}

/** Close account directive. */
export interface CloseDirective extends BaseDirective {
    type: 'close';
    account: string;
}

/** All directive types. */
export type Directive =
    | TransactionDirective
    | BalanceDirective
    | OpenDirective
    | CloseDirective
    | { type: 'commodity'; date: string; currency: string }
    | { type: 'pad'; date: string; account: string; source_account: string }
    | { type: 'event'; date: string; event_type: string; value: string }
    | { type: 'note'; date: string; account: string; comment: string }
    | { type: 'document'; date: string; account: string; path: string }
    | { type: 'price'; date: string; currency: string; amount: Amount }
    | { type: 'query'; date: string; name: string; query_string: string }
    | { type: 'custom'; date: string; custom_type: string };

/** Ledger options. */
export interface LedgerOptions {
    operating_currencies: string[];
    title?: string;
}

/** Parsed ledger. */
export interface Ledger {
    directives: Directive[];
    options: LedgerOptions;
}

/** Result of parsing a Beancount file. */
export interface ParseResult {
    ledger?: Ledger;
    errors: BeancountError[];
}

/** Result of validation. */
export interface ValidationResult {
    valid: boolean;
    errors: BeancountError[];
}

/** Cell value in query results. */
export type CellValue =
    | null
    | string
    | number
    | boolean
    | Amount
    | { units: Amount; cost?: { number: string; currency: string; date?: string; label?: string } }
    | { positions: Array<{ units: Amount }> }
    | string[];

/** Result of a BQL query. */
export interface QueryResult {
    columns: string[];
    rows: CellValue[][];
    errors: BeancountError[];
}

/** Result of formatting. */
export interface FormatResult {
    formatted?: string;
    errors: BeancountError[];
}

/** Result of pad expansion. */
export interface PadResult {
    directives: Directive[];
    padding_transactions: Directive[];
    errors: BeancountError[];
}

/** Result of running a plugin. */
export interface PluginResult {
    directives: Directive[];
    errors: BeancountError[];
}

/** Plugin information. */
export interface PluginInfo {
    name: string;
    description: string;
}

/** BQL completion suggestion. */
export interface Completion {
    text: string;
    category: string;
    description?: string;
}

/** Result of BQL completion request. */
export interface CompletionResult {
    completions: Completion[];
    context: string;
}

// =============================================================================
// Editor Integration Types (LSP-like features)
// =============================================================================

/** The kind of a completion item. */
export type EditorCompletionKind = 'keyword' | 'account' | 'accountsegment' | 'currency' | 'payee' | 'date' | 'text';

/** A completion item for Beancount source editing. */
export interface EditorCompletion {
    label: string;
    kind: EditorCompletionKind;
    detail?: string;
    insertText?: string;
}

/** Result of an editor completion request. */
export interface EditorCompletionResult {
    completions: EditorCompletion[];
    context: string;
}

/** A range in the document. */
export interface EditorRange {
    start_line: number;
    start_character: number;
    end_line: number;
    end_character: number;
}

/** Hover information for a symbol. */
export interface EditorHoverInfo {
    contents: string;
    range?: EditorRange;
}

/** A location in the document. */
export interface EditorLocation {
    line: number;
    character: number;
}

/** The kind of a symbol. */
export type SymbolKind = 'transaction' | 'account' | 'balance' | 'commodity' | 'posting' | 'pad' | 'event' | 'note' | 'document' | 'price' | 'query' | 'custom';

/** A document symbol for the outline view. */
export interface EditorDocumentSymbol {
    name: string;
    detail?: string;
    kind: SymbolKind;
    range: EditorRange;
    children?: EditorDocumentSymbol[];
    deprecated?: boolean;
}

/** The kind of reference. */
export type ReferenceKind = 'account' | 'currency' | 'payee';

/** A reference to a symbol in the document. */
export interface EditorReference {
    range: EditorRange;
    kind: ReferenceKind;
    is_definition: boolean;
    context?: string;
}

/** Result of a find-references request. */
export interface EditorReferencesResult {
    symbol: string;
    kind: ReferenceKind;
    references: EditorReference[];
}

/**
 * A parsed and validated ledger that caches the parse result.
 * Use this class when you need to perform multiple operations on the same
 * source without re-parsing each time.
 */
export class ParsedLedger {
    constructor(source: string);
    free(): void;

    /** Check if the ledger is valid (no parse or validation errors). */
    isValid(): boolean;

    /** Get all errors (parse + validation). */
    getErrors(): BeancountError[];

    /** Get parse errors only. */
    getParseErrors(): BeancountError[];

    /** Get validation errors only. */
    getValidationErrors(): BeancountError[];

    /** Get the parsed directives. */
    getDirectives(): Directive[];

    /** Get the ledger options. */
    getOptions(): LedgerOptions;

    /** Get the number of directives. */
    directiveCount(): number;

    /** Run a BQL query on this ledger. */
    query(queryStr: string): QueryResult;

    /** Get account balances (shorthand for query("BALANCES")). */
    balances(): QueryResult;

    /** Format the ledger source. */
    format(): FormatResult;

    /** Expand pad directives. */
    expandPads(): PadResult;

    /** Run a native plugin on this ledger. */
    runPlugin(pluginName: string): PluginResult;

    // =========================================================================
    // Editor Integration (LSP-like features)
    // =========================================================================

    /** Get completions at the given position. */
    getCompletions(line: number, character: number): EditorCompletionResult;

    /** Get hover information at the given position. */
    getHoverInfo(line: number, character: number): EditorHoverInfo | null;

    /** Get the definition location for the symbol at the given position. */
    getDefinition(line: number, character: number): EditorLocation | null;

    /** Get all document symbols for the outline view. */
    getDocumentSymbols(): EditorDocumentSymbol[];

    /** Find all references to the symbol at the given position. */
    getReferences(line: number, character: number): EditorReferencesResult | null;

    /** Serialize this ledger to a compact binary blob for caching. */
    serialize(): Uint8Array;

    /**
     * Restore a ParsedLedger from cached bytes.
     * The source must be the same text used when the cache was created.
     * Throws if the bytes are invalid or from a different library version.
     */
    static fromCache(bytes: Uint8Array, source: string): ParsedLedger;
}

/**
 * A fully processed multi-file ledger for queries and validation.
 * Use this class for ledgers spanning multiple files with include directives.
 * For single-file ledgers with editor features, use ParsedLedger instead.
 */
export class Ledger {
    free(): void;

    /** Create from multiple files with include resolution. */
    static fromFiles(files: FileMap, entryPoint: string): Ledger;

    /** Check if the ledger is valid (no errors). */
    isValid(): boolean;

    /** Get all errors. */
    getErrors(): BeancountError[];

    /** Get the parsed directives. */
    getDirectives(): Directive[];

    /** Get the ledger options. */
    getOptions(): LedgerOptions;

    /** Get the number of directives. */
    directiveCount(): number;

    /** Run a BQL query on this ledger. */
    query(queryStr: string): QueryResult;

    /** Get account balances (shorthand for query("BALANCES")). */
    balances(): QueryResult;

    /** Expand pad directives. */
    expandPads(): PadResult;

    /** Run a native plugin on this ledger. */
    runPlugin(pluginName: string): PluginResult;

    /** Get completions using cross-file data. Pass the source of the file being edited. */
    getCompletions(source: string, line: number, character: number): EditorCompletionResult;

    /** Serialize this ledger to a compact binary blob for caching. */
    serialize(): Uint8Array;

    /**
     * Restore a Ledger from cached bytes.
     * Throws if the bytes are invalid or from a different library version.
     */
    static fromCache(bytes: Uint8Array): Ledger;
}

// =============================================================================
// Multi-File API (for WASM environments without filesystem access)
// =============================================================================

/** Map of file paths to their contents. */
export type FileMap = Record<string, string>;

/**
 * Parse multiple Beancount files with include resolution.
 *
 * @param files - Object mapping file paths to their contents
 * @param entryPoint - The main file to start loading from (must exist in files)
 * @returns ParseResult with the combined ledger from all files
 *
 * @example
 * const result = parseMultiFile({
 *   "main.beancount": 'include "accounts.beancount"',
 *   "accounts.beancount": "2024-01-01 open Assets:Bank USD"
 * }, "main.beancount");
 */
export function parseMultiFile(files: FileMap, entryPoint: string): ParseResult;

/**
 * Validate multiple Beancount files with include resolution.
 *
 * @param files - Object mapping file paths to their contents
 * @param entryPoint - The main file to start loading from (must exist in files)
 * @returns ValidationResult indicating whether the combined ledger is valid
 */
export function validateMultiFile(files: FileMap, entryPoint: string): ValidationResult;

/**
 * Run a BQL query on multiple Beancount files.
 *
 * @param files - Object mapping file paths to their contents
 * @param entryPoint - The main file to start loading from (must exist in files)
 * @param query - The BQL query string to execute
 * @returns QueryResult with columns, rows, and any errors
 */
export function queryMultiFile(files: FileMap, entryPoint: string, query: string): QueryResult;

/**
 * Compute a SHA-256 fingerprint of one or more source strings.
 *
 * Returns a lowercase hex string. Store alongside serialized ledger bytes
 * and compare on next load; if the fingerprint changed, discard the cache.
 *
 * @param sources - Array of source strings
 * @returns Lowercase hex SHA-256 hash
 */
export function hashSources(sources: string[]): string;
"#;

// =============================================================================
// Initialization
// =============================================================================

/// Initialize the WASM module.
///
/// This sets up panic hooks for better error messages in the browser console.
/// Call this once before using any other functions.
#[wasm_bindgen(start)]
pub fn init() {
    // Set up panic hook for better error messages
    console_error_panic_hook::set_once();
}

// =============================================================================
// Tests
// =============================================================================

#[cfg(test)]
mod tests {
    use super::*;
    use rustledger_parser::parse as parse_beancount;
    use rustledger_validate::{Phase, ValidationOptions, ValidationSession};

    /// Test helper mirroring the deleted public `validate()`. Chains
    /// Early + Late + finalize through a single session against the
    /// same input.
    fn validate_ledger(
        directives: &[rustledger_core::Directive],
    ) -> Vec<rustledger_validate::ValidationError> {
        let today = rustledger_core::naive_date(2999, 12, 31).unwrap();
        let mut session = ValidationSession::new(ValidationOptions::default());
        let mut errors = session.run_phase(directives, Phase::Early, today);
        errors.extend(session.run_phase(directives, Phase::Late, today));
        errors.extend(session.finalize());
        errors
    }

    #[test]
    fn test_parse_simple() {
        let source = r#"
2024-01-01 open Assets:Bank USD

2024-01-15 * "Coffee Shop" "Morning coffee"
  Expenses:Food:Coffee  5.00 USD
  Assets:Bank          -5.00 USD
"#;

        let result = parse_beancount(source);
        assert!(result.errors.is_empty());
        assert_eq!(result.directives.len(), 2);
    }

    #[test]
    fn test_version() {
        let v = version();
        assert!(!v.is_empty());
    }

    #[test]
    fn test_load_and_book() {
        use helpers::load_and_book;

        // Valid ledger
        let source = r#"
2024-01-01 open Assets:Bank USD
2024-01-01 open Expenses:Food USD

2024-01-15 * "Coffee"
  Expenses:Food  5.00 USD
  Assets:Bank   -5.00 USD
"#;
        let load = load_and_book(source);
        assert!(load.errors.is_empty());
        assert_eq!(load.directives.len(), 3);

        // Invalid ledger (unopened account)
        let source = r#"
2024-01-01 open Assets:Bank USD

2024-01-15 * "Coffee"
  Expenses:Food  5.00 USD
  Assets:Bank   -5.00 USD
"#;
        let load = load_and_book(source);
        assert!(load.errors.is_empty()); // Parse succeeds
        let validation_errors = validate_ledger(&load.directives);
        assert!(
            !validation_errors.is_empty(),
            "should detect Expenses:Food not opened"
        );
    }

    // =========================================================================
    // Multi-file API tests
    // =========================================================================

    #[test]
    fn test_multi_file_include_resolution() {
        use rustledger_loader::{Loader, VirtualFileSystem};
        use std::path::Path;

        let mut vfs = VirtualFileSystem::new();
        vfs.add_file(
            "main.beancount",
            r#"
include "accounts.beancount"

2024-01-15 * "Coffee"
  Expenses:Food  5.00 USD
  Assets:Bank   -5.00 USD
"#,
        );
        vfs.add_file(
            "accounts.beancount",
            r"
2024-01-01 open Assets:Bank USD
2024-01-01 open Expenses:Food USD
",
        );

        let mut loader = Loader::new().with_filesystem(Box::new(vfs));
        let result = loader.load(Path::new("main.beancount")).unwrap();

        assert!(result.errors.is_empty(), "should have no errors");
        // 2 opens + 1 transaction = 3 directives
        assert_eq!(result.directives.len(), 3);
    }

    #[test]
    fn test_multi_file_nested_includes() {
        use rustledger_loader::{Loader, VirtualFileSystem};
        use std::path::Path;

        let mut vfs = VirtualFileSystem::new();
        vfs.add_file("main.beancount", r#"include "accounts/index.beancount""#);
        vfs.add_file(
            "accounts/index.beancount",
            r#"
include "assets.beancount"
include "expenses.beancount"
"#,
        );
        vfs.add_file(
            "accounts/assets.beancount",
            "2024-01-01 open Assets:Bank USD",
        );
        vfs.add_file(
            "accounts/expenses.beancount",
            "2024-01-01 open Expenses:Food USD",
        );

        let mut loader = Loader::new().with_filesystem(Box::new(vfs));
        let result = loader.load(Path::new("main.beancount")).unwrap();

        assert!(result.errors.is_empty(), "should have no errors");
        assert_eq!(result.directives.len(), 2); // 2 open directives
    }

    #[test]
    fn test_multi_file_validation() {
        use rustledger_booking::BookingEngine;
        use rustledger_core::Directive;
        use rustledger_loader::{Loader, VirtualFileSystem};
        use std::path::Path;

        let mut vfs = VirtualFileSystem::new();
        vfs.add_file(
            "main.beancount",
            r#"
include "accounts.beancount"

2024-01-15 * "Coffee"
  Expenses:Food  5.00 USD
  Assets:Bank
"#,
        );
        vfs.add_file(
            "accounts.beancount",
            r"
2024-01-01 open Assets:Bank USD
2024-01-01 open Expenses:Food USD
",
        );

        let mut loader = Loader::new().with_filesystem(Box::new(vfs));
        let result = loader.load(Path::new("main.beancount")).unwrap();

        assert!(result.errors.is_empty());

        // Extract directives and book transactions
        let mut directives: Vec<_> = result.directives.into_iter().map(|s| s.value).collect();
        let mut engine = BookingEngine::new();
        engine.register_account_methods(directives.iter());
        for directive in &mut directives {
            if let Directive::Transaction(txn) = directive
                && let Ok(result) = engine.book_and_interpolate(txn)
            {
                engine.apply(&result.transaction);
                *txn = result.transaction;
            }
        }
        // Sort by date for proper validation
        directives.sort_by_key(rustledger_core::Directive::date);
        let validation_errors = validate_ledger(&directives);
        assert!(
            validation_errors.is_empty(),
            "ledger should be valid, but got: {validation_errors:?}"
        );
    }

    /// Test `ParsedLedger` multi-file construction via `process()` pipeline.
    #[test]
    fn test_parsed_ledger_multi_file_via_process() {
        use rustledger_core::Directive;
        use rustledger_loader::{FileSystem, LoadOptions, Loader, VirtualFileSystem, process};
        use std::path::Path;

        let mut vfs = VirtualFileSystem::new();
        vfs.add_file(
            "main.beancount",
            r#"
include "accounts.beancount"

2024-01-15 * "Coffee"
  Expenses:Food  5.00 USD
  Assets:Bank
"#,
        );
        vfs.add_file(
            "accounts.beancount",
            r"
2024-01-01 open Assets:Bank USD
2024-01-01 open Expenses:Food USD
",
        );

        assert!(vfs.exists(Path::new("main.beancount")));

        let mut loader = Loader::new().with_filesystem(Box::new(vfs));
        let raw = loader.load(Path::new("main.beancount")).unwrap();

        let options = LoadOptions {
            validate: true,
            ..Default::default()
        };

        let ledger = process(raw, &options).unwrap();
        let directives: Vec<_> = ledger.directives.into_iter().map(|s| s.value).collect();

        // Should have 2 opens + 1 transaction = 3 directives
        assert_eq!(directives.len(), 3);

        // Should be sorted by date
        let dates: Vec<_> = directives
            .iter()
            .map(rustledger_core::Directive::date)
            .collect();
        assert!(dates.windows(2).all(|w| w[0] <= w[1]));

        // Transaction should have interpolated bank amount
        let txn = directives
            .iter()
            .find_map(|d| match d {
                Directive::Transaction(t) => Some(t),
                _ => None,
            })
            .expect("should have transaction");

        let bank = txn
            .postings
            .iter()
            .find(|p| p.account.as_str().contains("Bank"))
            .expect("should have bank posting");
        assert!(
            bank.units
                .as_ref()
                .and_then(rustledger_core::IncompleteAmount::number)
                .is_some(),
            "bank amount should be interpolated"
        );

        // No errors
        assert!(ledger.errors.is_empty(), "errors: {:?}", ledger.errors);
    }

    /// Regression test for #659: total cost `{{ }}` syntax must produce per-unit cost.
    #[test]
    fn test_total_cost_produces_per_unit_cost() {
        use helpers::load_and_book;
        use rustledger_core::Directive;
        use std::str::FromStr;

        let source = r#"
2020-01-01 open Assets:Investments:PROP PROP
2020-01-01 open Assets:Bank AUD

2020-01-16 * "Buy PROP"
  Assets:Investments:PROP  273.2200 PROP {{150.00 AUD}}
  Assets:Bank              -150.00 AUD
"#;
        let load = load_and_book(source);
        assert!(load.errors.is_empty(), "errors: {:?}", load.errors);

        // Find the transaction and check that cost has number_per set
        let txn = load
            .directives
            .iter()
            .find_map(|d| match d {
                Directive::Transaction(txn) => Some(txn),
                _ => None,
            })
            .expect("should have at least one transaction");

        let prop_posting = txn
            .postings
            .iter()
            .find(|p| {
                p.units
                    .as_ref()
                    .is_some_and(|u| u.currency() == Some("PROP"))
            })
            .expect("should have PROP posting");

        let cost = prop_posting.cost.as_ref().expect("should have cost");
        let per_unit = cost
            .number_per
            .expect("total cost {{}} should be converted to per-unit cost, but number_per is None");

        // 150.00 / 273.2200 ≈ 0.5490
        let expected = rustledger_core::Decimal::from_str("0.5490").unwrap();
        let diff = (per_unit - expected).abs();
        assert!(
            diff < rustledger_core::Decimal::from_str("0.001").unwrap(),
            "per-unit cost should be ~0.5490, got {per_unit}"
        );
    }

    // =========================================================================
    // Pipeline parity tests: verify WASM produces same results as CLI
    // =========================================================================

    /// Helper: process source through CLI pipeline and return directives.
    fn cli_process(source: &str) -> Vec<rustledger_core::Directive> {
        use rustledger_loader::{LoadOptions, Loader, VirtualFileSystem, process};
        use std::path::Path;

        let mut vfs = VirtualFileSystem::new();
        vfs.add_file("test.beancount", source);
        let mut loader = Loader::new().with_filesystem(Box::new(vfs));
        let raw = loader.load(Path::new("test.beancount")).unwrap();
        let options = LoadOptions {
            validate: false,
            ..Default::default()
        };
        let ledger = process(raw, &options).unwrap();
        ledger.directives.into_iter().map(|s| s.value).collect()
    }

    /// Helper: process source through WASM pipeline and return directives.
    fn wasm_process(source: &str) -> Vec<rustledger_core::Directive> {
        let load = helpers::load_and_book(source);
        assert!(load.errors.is_empty(), "WASM errors: {:?}", load.errors);
        load.directives
    }

    /// Parity: out-of-order transactions should be sorted by date.
    #[test]
    fn test_parity_sorting() {
        use rustledger_core::Directive;

        let source = r#"
2024-01-01 open Assets:Bank USD
2024-01-01 open Expenses:Food USD

2024-03-01 * "March"
  Expenses:Food  30 USD
  Assets:Bank

2024-01-15 * "January"
  Expenses:Food  10 USD
  Assets:Bank

2024-02-15 * "February"
  Expenses:Food  20 USD
  Assets:Bank
"#;
        let cli = cli_process(source);
        let wasm = wasm_process(source);

        // Both should have same directive count
        assert_eq!(cli.len(), wasm.len(), "directive count mismatch");

        // Both should be sorted by date
        let cli_dates: Vec<_> = cli.iter().map(rustledger_core::Directive::date).collect();
        let wasm_dates: Vec<_> = wasm.iter().map(rustledger_core::Directive::date).collect();
        assert_eq!(cli_dates, wasm_dates, "date order mismatch");

        // Verify transactions are in chronological order
        let txn_dates: Vec<_> = wasm
            .iter()
            .filter_map(|d| match d {
                Directive::Transaction(t) => Some(t.date),
                _ => None,
            })
            .collect();
        assert!(
            txn_dates.windows(2).all(|w| w[0] <= w[1]),
            "transactions not sorted: {txn_dates:?}"
        );
    }

    /// Parity: total cost `{{ }}` produces identical per-unit costs.
    #[test]
    fn test_parity_total_cost() {
        fn get_cost_per_unit(
            directives: &[rustledger_core::Directive],
        ) -> rustledger_core::Decimal {
            directives
                .iter()
                .find_map(|d| match d {
                    rustledger_core::Directive::Transaction(t) => t
                        .postings
                        .iter()
                        .find_map(|p| p.cost.as_ref().and_then(|c| c.number_per)),
                    _ => None,
                })
                .expect("should have a cost")
        }

        let source = r#"
2020-01-01 open Assets:Investments PROP
2020-01-01 open Assets:Bank AUD

2020-01-16 * "Buy"
  Assets:Investments  273.2200 PROP {{150.00 AUD}}
  Assets:Bank         -150.00 AUD
"#;
        let cli = cli_process(source);
        let wasm = wasm_process(source);

        assert_eq!(
            get_cost_per_unit(&cli),
            get_cost_per_unit(&wasm),
            "per-unit cost differs between CLI and WASM"
        );
    }

    /// Parity: interpolation fills in missing amounts identically.
    #[test]
    fn test_parity_interpolation() {
        fn get_bank_amount(directives: &[rustledger_core::Directive]) -> rustledger_core::Decimal {
            directives
                .iter()
                .find_map(|d| match d {
                    rustledger_core::Directive::Transaction(t) => t.postings.iter().find_map(|p| {
                        if p.account.as_str().contains("Bank") {
                            p.units
                                .as_ref()
                                .and_then(rustledger_core::IncompleteAmount::number)
                        } else {
                            None
                        }
                    }),
                    _ => None,
                })
                .expect("should have bank posting with amount")
        }

        let source = r#"
2024-01-01 open Assets:Bank USD
2024-01-01 open Expenses:Food USD

2024-01-15 * "Coffee"
  Expenses:Food  5.00 USD
  Assets:Bank
"#;
        let cli = cli_process(source);
        let wasm = wasm_process(source);

        assert_eq!(
            get_bank_amount(&cli),
            get_bank_amount(&wasm),
            "interpolated amount differs"
        );
    }

    /// Parity: pad directives produce correct padding transactions.
    #[test]
    fn test_parity_pad_expansion() {
        use rustledger_booking::expand_pads;

        let source = r"
2024-01-01 open Assets:Bank USD
2024-01-01 open Equity:Opening USD

2024-01-01 pad Assets:Bank Equity:Opening
2024-01-15 balance Assets:Bank 1000 USD
";
        let cli = cli_process(source);
        let wasm = wasm_process(source);

        let cli_expanded = expand_pads(&cli);
        let wasm_expanded = expand_pads(&wasm);

        assert_eq!(
            cli_expanded.len(),
            wasm_expanded.len(),
            "expanded directive count differs"
        );
    }

    // =========================================================================
    // Serialization / Caching roundtrip tests
    // =========================================================================

    #[test]
    fn test_parsed_ledger_serialize_roundtrip() {
        use crate::cache;
        use crate::editor::EditorCache;
        use crate::helpers::load_and_book;

        let source = r#"
option "title" "Cache Test"
option "operating_currency" "USD"

2024-01-01 open Assets:Bank USD
2024-01-01 open Expenses:Food USD

2024-01-15 * "Coffee" "Morning latte"
  Expenses:Food  5.00 USD
  Assets:Bank   -5.00 USD

2024-01-20 * "Groceries"
  Expenses:Food  42.50 USD
  Assets:Bank   -42.50 USD
"#;

        // Build the payload the same way ParsedLedger.serialize() does
        let processed = load_and_book(source);
        let payload = cache::ParsedLedgerPayload {
            directives: processed.directives.clone(),
            options: processed.options.clone(),
            parse_errors: Vec::new(),
            validation_errors: Vec::new(),
        };

        let bytes = cache::serialize_parsed(&payload).expect("serialize");
        let restored = cache::deserialize_parsed(&bytes).expect("deserialize");

        assert_eq!(
            restored.directives.len(),
            processed.directives.len(),
            "directive count should match after roundtrip"
        );
        assert_eq!(
            restored.options.title.as_deref(),
            Some("Cache Test"),
            "title preserved"
        );
        assert_eq!(
            restored.options.operating_currencies,
            ["USD"],
            "operating currencies preserved"
        );

        // Verify the from_cache path works (re-parses source for editor features)
        let parse_result = rustledger_parser::parse(source);
        let editor_cache = EditorCache::new(source, &parse_result);
        assert!(
            !editor_cache.accounts.is_empty(),
            "editor cache should have accounts after re-parse"
        );
    }

    #[test]
    fn test_ledger_serialize_roundtrip() {
        use crate::cache;
        use crate::helpers::load_and_book;

        let source = r#"
option "title" "Multi Cache"
option "operating_currency" "EUR"

2024-01-01 open Assets:Bank EUR
2024-01-01 open Expenses:Rent EUR

2024-02-01 * "Rent"
  Expenses:Rent  800 EUR
  Assets:Bank   -800 EUR
"#;

        let processed = load_and_book(source);
        let payload = cache::LedgerPayload {
            directives: processed.directives.clone(),
            options: processed.options.clone(),
            errors: Vec::new(),
        };

        let bytes = cache::serialize_ledger(&payload).expect("serialize");
        let restored = cache::deserialize_ledger(&bytes).expect("deserialize");

        assert_eq!(
            restored.directives.len(),
            processed.directives.len(),
            "directive count should match after roundtrip"
        );
        assert_eq!(restored.options.title.as_deref(), Some("Multi Cache"));

        // Verify EditorCache can be rebuilt from restored directives
        let editor_cache = crate::editor::EditorCache::from_directives(&restored.directives);
        assert!(
            !editor_cache.accounts.is_empty(),
            "editor cache should have accounts from restored directives"
        );
    }

    #[test]
    fn test_serialize_rejects_corrupted_bytes() {
        use crate::cache;

        // Bad magic
        assert!(cache::deserialize_ledger(b"GARBAGE_DATA_HERE").is_err());
        assert!(cache::deserialize_parsed(b"GARBAGE_DATA_HERE").is_err());

        // Too short
        assert!(cache::deserialize_ledger(b"short").is_err());
    }

    #[test]
    fn test_hash_sources_api() {
        let h1 = hash_sources(vec!["source v1".to_string()]);
        let h2 = hash_sources(vec!["source v1".to_string()]);
        let h3 = hash_sources(vec!["source v2".to_string()]);

        assert_eq!(h1, h2, "same content → same hash");
        assert_ne!(h1, h3, "different content → different hash");
        assert_eq!(h1.len(), 64, "SHA-256 produces 64 hex chars");
    }
}
