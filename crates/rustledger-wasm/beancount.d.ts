// TypeScript Type Definitions for beancount-wasm
//
// This file provides type definitions for the beancount-wasm WebAssembly module.
// Import and use with the wasm-bindgen generated JavaScript bindings.
//
// Usage:
//   import init, { parse, validate_source, query, version } from 'beancount-wasm';
//   await init();
//   const result = parse(source);

/**
 * Result of parsing a Beancount source string.
 */
export interface ParseResult {
  /** The parsed ledger (if any parsing succeeded). */
  ledger: Ledger | null;
  /** Parse errors encountered. */
  errors: Error[];
}

/**
 * A parsed Beancount ledger.
 */
export interface Ledger {
  /** All directives in the ledger. */
  directives: DirectiveJson[];
  /** Ledger options. */
  options: LedgerOptions;
}

/**
 * Ledger options extracted from option directives.
 */
export interface LedgerOptions {
  /** Operating currencies for value conversions. */
  operating_currencies: string[];
  /** Ledger title. */
  title: string | null;
}

/**
 * A Beancount directive in JSON form.
 */
export interface DirectiveJson {
  /** Type of directive: "transaction", "open", "close", "balance", etc. */
  type: DirectiveType;
  /** Directive date in YYYY-MM-DD format. */
  date: string;
  /**
   * User-defined metadata key/value pairs (issue #1168).
   *
   * Absent when the directive has no explicit metadata in the source.
   * Values are strings, booleans, `{number, currency}` Amount objects,
   * or `null`. Strong host types — Account, Currency, Tag, Link, Date,
   * Decimal — flatten to JSON strings; use the value's directive
   * context to interpret them.
   */
  meta?: Record<string, MetaValueJson>;
  /** Additional directive-specific fields (see directive type interfaces). */
  [key: string]: unknown;
}

/**
 * Metadata-value wire format (issue #1168).
 *
 * Untagged union — JS consumers branch on `typeof v` (`'string'` /
 * `'boolean'`) or on object shape (`'number' in v` → Amount) without
 * a discriminator field. Mirrors the FFI-WASI shape so portable
 * clients see identical metadata values across both bindings.
 */
export type MetaValueJson =
  | string
  | boolean
  | { number: string; currency: string }
  | null;

/**
 * Possible directive types.
 */
export type DirectiveType =
  | "transaction"
  | "open"
  | "close"
  | "balance"
  | "commodity"
  | "pad"
  | "event"
  | "note"
  | "document"
  | "price"
  | "query"
  | "custom";

/**
 * Transaction directive data.
 */
export interface TransactionData {
  type: "transaction";
  date: string;
  /** Transaction flag: "*" for complete, "!" for flagged. */
  flag: string;
  /** Optional payee. */
  payee: string | null;
  /** Transaction description. */
  narration: string;
  /** Tags (without # prefix). */
  tags: string[];
  /** Links (without ^ prefix). */
  links: string[];
  /** Transaction postings. */
  postings: Posting[];
  /** Transaction-level metadata (issue #1168). */
  meta?: Record<string, MetaValueJson>;
}

/**
 * A transaction posting.
 */
export interface Posting {
  /** Account name. */
  account: string;
  /** Units (amount). */
  units: Amount | null;
  /** Optional cost specification. */
  cost: CostSpec | null;
  /** Posting-level metadata (issue #1168). */
  meta?: Record<string, MetaValueJson>;
}

/**
 * An amount with number and currency.
 */
export interface Amount {
  /** Decimal number as string for precision. */
  number: string;
  /** Currency code. */
  currency: string;
}

/**
 * Cost-number tagged enum mirroring `rustledger_core::CostNumber`.
 * Discriminate via the `kind` field; never probe for present-but-null fields.
 */
export type CostNumber =
  | { kind: 'per_unit'; value: string }
  | { kind: 'total'; value: string }
  | { kind: 'per_unit_from_total'; per_unit: string; total: string };

/**
 * Cost specification for a posting.
 */
export interface CostSpec {
  /** Cost number (per-unit, total, or post-booking pair). */
  number: CostNumber | null;
  /** Cost currency. */
  currency: string | null;
  /** Acquisition date. */
  date: string | null;
  /** Lot label. */
  label: string | null;
}

/**
 * Open directive data.
 */
export interface OpenData {
  type: "open";
  date: string;
  /** Account name. */
  account: string;
  /** Allowed currencies. */
  currencies: string[];
  /** Booking method. */
  booking: string | null;
  /** Open-directive metadata (issue #1168). */
  meta?: Record<string, MetaValueJson>;
}

/**
 * Close directive data.
 */
export interface CloseData {
  type: "close";
  date: string;
  /** Account name. */
  account: string;
  /** Close-directive metadata (issue #1168). */
  meta?: Record<string, MetaValueJson>;
}

/**
 * Balance assertion directive data.
 */
export interface BalanceData {
  type: "balance";
  date: string;
  /** Account name. */
  account: string;
  /** Expected balance amount. */
  amount: Amount;
  /** Balance-directive metadata (issue #1168). */
  meta?: Record<string, MetaValueJson>;
}

/**
 * Commodity declaration directive data.
 */
export interface CommodityData {
  type: "commodity";
  date: string;
  /** Currency code. */
  currency: string;
  /** Commodity-directive metadata (issue #1168). */
  meta?: Record<string, MetaValueJson>;
}

/**
 * Pad directive data.
 */
export interface PadData {
  type: "pad";
  date: string;
  /** Account to pad. */
  account: string;
  /** Source account for padding. */
  source_account: string;
  /** Pad-directive metadata (issue #1168). */
  meta?: Record<string, MetaValueJson>;
}

/**
 * Event directive data.
 */
export interface EventData {
  type: "event";
  date: string;
  /** Event type (e.g., "location"). */
  event_type: string;
  /** Event value. */
  value: string;
  /** Event-directive metadata (issue #1168). */
  meta?: Record<string, MetaValueJson>;
}

/**
 * Note directive data.
 */
export interface NoteData {
  type: "note";
  date: string;
  /** Account name. */
  account: string;
  /** Note content. */
  comment: string;
  /** Note-directive metadata (issue #1168). */
  meta?: Record<string, MetaValueJson>;
}

/**
 * Document directive data.
 */
export interface DocumentData {
  type: "document";
  date: string;
  /** Account name. */
  account: string;
  /** Path to document file. */
  path: string;
  /** Document-directive metadata (issue #1168). */
  meta?: Record<string, MetaValueJson>;
}

/**
 * Price directive data.
 */
export interface PriceData {
  type: "price";
  date: string;
  /** Currency being priced. */
  currency: string;
  /** Price amount. */
  amount: Amount;
  /** Price-directive metadata (issue #1168). */
  meta?: Record<string, MetaValueJson>;
}

/**
 * Query directive data.
 */
export interface QueryDirectiveData {
  type: "query";
  date: string;
  /** Query name. */
  name: string;
  /** BQL query string. */
  query: string;
  /** Query-directive metadata (issue #1168). */
  meta?: Record<string, MetaValueJson>;
}

/**
 * Custom directive data.
 */
export interface CustomData {
  type: "custom";
  date: string;
  /** Custom type name. */
  custom_type: string;
  /**
   * Positional values after the custom type keyword (issue #1168).
   * Pre-#1168 these were dropped entirely from the JSON output.
   */
  values?: MetaValueJson[];
  /** Custom-directive metadata (issue #1168). */
  meta?: Record<string, MetaValueJson>;
}

/**
 * An error with optional source location.
 */
export interface Error {
  /** Error message. */
  message: string;
  /** Line number (1-based). */
  line: number | null;
  /** Column number (1-based). */
  column: number | null;
  /** Error severity: "error" or "warning". */
  severity: "error" | "warning";
}

/**
 * Result of validation.
 */
export interface ValidationResult {
  /** Whether the ledger is valid. */
  valid: boolean;
  /** Validation errors. */
  errors: Error[];
}

/**
 * Result of a BQL query.
 */
export interface QueryResult {
  /** Column names. */
  columns: string[];
  /** Result rows. */
  rows: QueryValue[][];
  /** Query errors. */
  errors: Error[];
}

/**
 * A value in a query result row.
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
  /** Units held. */
  units: Amount;
  /** Optional cost basis. */
  cost: Cost | null;
}

/**
 * Cost basis for a position.
 */
export interface Cost {
  /** Per-unit cost. */
  number: string;
  /** Cost currency. */
  currency: string;
  /** Acquisition date. */
  date: string | null;
  /** Lot label. */
  label: string | null;
}

/**
 * An inventory of positions.
 */
export interface Inventory {
  /** All positions in the inventory. */
  positions: Position[];
}

// === WASM Module Exports ===

/**
 * Parse a Beancount source string.
 *
 * @param source - The Beancount source text to parse.
 * @returns Parse result containing the ledger and any errors.
 *
 * @example
 * ```typescript
 * const result = parse(`
 *   2024-01-01 open Assets:Bank USD
 *   2024-01-15 * "Coffee"
 *     Expenses:Food  5.00 USD
 *     Assets:Bank   -5.00 USD
 * `);
 *
 * if (result.errors.length === 0) {
 *   console.log('Parsed', result.ledger.directives.length, 'directives');
 * }
 * ```
 */
export function parse(source: string): ParseResult;

/**
 * Validate a parsed ledger.
 *
 * Takes a JSON-serialized ledger and validates it against Beancount rules.
 *
 * @param ledger_json - JSON string of a Ledger object.
 * @returns Validation result with any errors found.
 *
 * @example
 * ```typescript
 * const parseResult = parse(source);
 * if (parseResult.ledger) {
 *   const ledgerJson = JSON.stringify(parseResult.ledger);
 *   const validation = validate(ledgerJson);
 *   if (!validation.valid) {
 *     console.error('Validation errors:', validation.errors);
 *   }
 * }
 * ```
 */
export function validate(ledger_json: string): ValidationResult;

/**
 * Parse and validate a Beancount source string in one step.
 *
 * This is more convenient than calling parse() and validate() separately.
 *
 * @param source - The Beancount source text to parse and validate.
 * @returns Validation result with parse and validation errors.
 *
 * @example
 * ```typescript
 * const result = validate_source(source);
 * if (result.valid) {
 *   console.log('Ledger is valid!');
 * } else {
 *   result.errors.forEach(e => console.error(e.message));
 * }
 * ```
 */
export function validate_source(source: string): ValidationResult;

/**
 * Run a BQL query on a Beancount source string.
 *
 * @param source - The Beancount source text.
 * @param query_str - The BQL query to execute.
 * @returns Query result with columns and rows.
 *
 * @example
 * ```typescript
 * const result = query(source, 'SELECT account, SUM(position) WHERE account ~ "Expenses:" GROUP BY account');
 * console.log('Columns:', result.columns);
 * result.rows.forEach(row => console.log(row));
 * ```
 */
export function query(source: string, query_str: string): QueryResult;

/**
 * Get the version of the beancount-wasm library.
 *
 * @returns Version string (e.g., "0.1.0").
 */
export function version(): string;

/**
 * Initialize the WASM module.
 *
 * Must be called before using any other functions.
 *
 * @returns Promise that resolves when initialization is complete.
 */
export default function init(): Promise<void>;
