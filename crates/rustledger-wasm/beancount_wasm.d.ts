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
    /** Directive-specific data (varies by type) */
    [key: string]: unknown;
}

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
 */
export interface Posting {
    /** Account name */
    account: string;
    /** Amount (may be null for auto-balanced postings) */
    units?: Amount | null;
    /** Cost specification */
    cost?: CostSpec | null;
    /** Posting flag */
    flag?: string;
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
 * A cost specification.
 */
export interface CostSpec {
    /** Per-unit cost */
    number_per?: string;
    /** Total cost */
    number_total?: string;
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
