/**
 * TypeScript type definitions for beancount-wasm
 *
 * These definitions describe the API exposed by the WASM module.
 */

/**
 * Initialize the WASM module.
 * Must be called before using any other functions.
 */
export function init(): Promise<void>;

/**
 * Parse a Beancount source string.
 * @param source - The Beancount source code
 * @returns ParseResult containing the ledger and any errors
 */
export function parse(source: string): ParseResult;

/**
 * Validate a Beancount source string.
 * Parses and validates in one step.
 * @param source - The Beancount source code
 * @returns ValidationResult with validity status and errors
 */
export function validate_source(source: string): ValidationResult;

/**
 * Validate a parsed ledger JSON.
 * @param ledger_json - JSON string of a parsed ledger
 * @returns ValidationResult with validity status and errors
 */
export function validate(ledger_json: string): ValidationResult;

/**
 * Execute a BQL query on a Beancount source string.
 * @param source - The Beancount source code
 * @param query - The BQL query string
 * @returns QueryResult with columns, rows, and errors
 */
export function query(source: string, query: string): QueryResult;

/**
 * Get the version of the beancount-wasm library.
 * @returns Version string (e.g., "0.1.0")
 */
export function version(): string;

// Type definitions

/**
 * Result of parsing a Beancount file.
 */
export interface ParseResult {
    /** The parsed ledger (present even if there are errors) */
    ledger: Ledger | null;
    /** Parse errors */
    errors: Error[];
}

/**
 * A parsed Beancount ledger.
 */
export interface Ledger {
    /** All directives in the ledger */
    directives: Directive[];
    /** Ledger options */
    options: LedgerOptions;
}

/**
 * Ledger configuration options.
 */
export interface LedgerOptions {
    /** Operating currencies (e.g., ["USD", "EUR"]) */
    operating_currencies: string[];
    /** Ledger title */
    title?: string;
}

/**
 * A Beancount directive.
 */
export interface Directive {
    /** Directive type: "transaction", "balance", "open", "close", etc. */
    type: DirectiveType;
    /** Date in YYYY-MM-DD format */
    date: string;
    /**
     * User-defined metadata key/value pairs (issue #1168).
     *
     * Absent when the directive has no explicit metadata. Values
     * follow the [`MetaValueJson`] shape: strings, booleans, Amount
     * `{number, currency}` objects, or `null`.
     */
    meta?: Record<string, MetaValueJson>;
    /** Directive-specific data (varies by type) */
    [key: string]: unknown;
}

/**
 * Metadata-value wire format (issue #1168). Untagged union.
 *
 * Branch on `typeof v` (`'string'` / `'boolean'`) or object shape
 * (`'number' in v` → Amount). Mirrors the FFI-WASI bindings'
 * metadata shape so portable consumers see the same value type
 * regardless of which binding they target.
 */
export type MetaValueJson =
    | string
    | boolean
    | { number: string; currency: string }
    | null;

/**
 * Valid directive types.
 */
export type DirectiveType =
    | "transaction"
    | "balance"
    | "open"
    | "close"
    | "commodity"
    | "pad"
    | "event"
    | "note"
    | "document"
    | "price"
    | "query"
    | "custom";

/**
 * A transaction directive.
 */
export interface TransactionDirective extends Directive {
    type: "transaction";
    /** Transaction flag (* or !) */
    flag: string;
    /** Optional payee */
    payee?: string;
    /** Transaction narration/description */
    narration: string;
    /** Transaction tags */
    tags: string[];
    /** Transaction links */
    links: string[];
    /** Transaction postings */
    postings: Posting[];
}

/**
 * A posting within a transaction.
 *
 * Field order mirrors `rustledger_wasm::types::PostingJson` so that
 * the type definitions read in the same order as the JSON output.
 */
export interface Posting {
    /** Account name */
    account: string;
    /** Amount (may be null for auto-balanced postings) */
    units?: Amount | null;
    /** Cost specification */
    cost?: CostSpec | null;
    /** Price annotation (`@` per-unit or `@@` total) */
    price?: Amount;
    /** Posting flag (e.g. "!" for pending) */
    flag?: string;
    /** Posting-level metadata (issue #1168) */
    meta?: Record<string, MetaValueJson>;
}

/**
 * An amount (number + currency).
 */
export interface Amount {
    /** Numeric value as string (to preserve precision) */
    number: string;
    /** Currency code */
    currency: string;
}

/**
 * Cost-number tagged enum mirroring `rustledger_core::CostNumber`.
 * Discriminate via the `kind` field.
 */
export type CostNumber =
    | { kind: 'per_unit'; value: string }
    | { kind: 'total'; value: string }
    | { kind: 'per_unit_from_total'; per_unit: string; total: string };

/**
 * A cost specification.
 */
export interface CostSpec {
    /** Cost number (per-unit, total, or post-booking pair) */
    number?: CostNumber;
    /** Cost currency */
    currency?: string;
    /** Acquisition date */
    date?: string;
    /** Lot label */
    label?: string;
}

/**
 * A balance directive.
 */
export interface BalanceDirective extends Directive {
    type: "balance";
    /** Account to check */
    account: string;
    /** Expected balance amount */
    amount: Amount;
    /** Explicit tolerance (e.g. "0.01" from `~ 0.01`), stringified for precision. */
    tolerance?: string;
}

/**
 * An open directive.
 */
export interface OpenDirective extends Directive {
    type: "open";
    /** Account to open */
    account: string;
    /** Allowed currencies */
    currencies: string[];
    /** Booking method */
    booking?: string;
}

/**
 * A close directive.
 */
export interface CloseDirective extends Directive {
    type: "close";
    /** Account to close */
    account: string;
}

/**
 * A price directive.
 */
export interface PriceDirective extends Directive {
    type: "price";
    /** Base currency */
    currency: string;
    /** Price amount */
    amount: Amount;
}

/**
 * A commodity declaration.
 */
export interface CommodityDirective extends Directive {
    type: "commodity";
    /** Currency being declared */
    currency: string;
}

/**
 * A pad directive — fills `account` from `source_account` to make the
 * next balance assertion pass.
 */
export interface PadDirective extends Directive {
    type: "pad";
    /** Account being padded */
    account: string;
    /** Source account the pad draws from */
    source_account: string;
}

/**
 * An event directive — records a named state value at a date.
 */
export interface EventDirective extends Directive {
    type: "event";
    /** Event name (e.g. "location") */
    event_type: string;
    /** Event value */
    value: string;
}

/**
 * A note directive — attaches a free-form comment to an account.
 */
export interface NoteDirective extends Directive {
    type: "note";
    /** Account the note applies to */
    account: string;
    /** Comment text */
    comment: string;
}

/**
 * A document directive — links an account to an external file path.
 */
export interface DocumentDirective extends Directive {
    type: "document";
    /** Account the document applies to */
    account: string;
    /** Path to the document file */
    path: string;
}

/**
 * A query directive — embeds a named BQL query in the ledger.
 */
export interface QueryDirective extends Directive {
    type: "query";
    /** Query name */
    name: string;
    /** BQL query text */
    query_string: string;
}

/**
 * A custom directive — `custom TYPE arg1 arg2 ...`. `values` carries
 * the positional arguments after the type keyword (absent when there
 * are none); each value is a [`MetaValueJson`].
 */
export interface CustomDirective extends Directive {
    type: "custom";
    /** Custom type keyword (the first word after `custom`) */
    custom_type: string;
    /** Positional values after the type keyword */
    values?: MetaValueJson[];
}

/**
 * An error with source location.
 */
export interface Error {
    /** Error message */
    message: string;
    /** Line number (1-based) */
    line?: number;
    /** Column number (1-based) */
    column?: number;
    /** Error severity: "error" or "warning" */
    severity: "error" | "warning";
}

/**
 * Result of validation.
 */
export interface ValidationResult {
    /** Whether the ledger is valid */
    valid: boolean;
    /** Validation errors */
    errors: Error[];
}

/**
 * Result of a BQL query.
 */
export interface QueryResult {
    /** Column names */
    columns: string[];
    /** Result rows (each row is an array of values) */
    rows: QueryValue[][];
    /** Query errors */
    errors: Error[];
}

/**
 * A value in a query result.
 * Can be a string, number, boolean, null, or object (for amounts/positions).
 */
export type QueryValue =
    | string
    | number
    | boolean
    | null
    | Amount
    | Position
    | Inventory;

/**
 * A position (amount with optional cost).
 */
export interface Position {
    /** Units held */
    units: Amount;
    /** Acquisition cost */
    cost?: {
        number: string;
        currency: string;
        date?: string;
        label?: string;
    };
}

/**
 * An inventory (collection of positions).
 */
export interface Inventory {
    /** All positions */
    positions: Position[];
}
