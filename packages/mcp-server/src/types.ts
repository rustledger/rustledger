// Type definitions for the MCP server

export interface Amount {
  number: string;
  currency: string;
}

export interface Posting {
  account: string;
  units?: Amount;
}

export interface BaseDirective {
  type: string;
  date: string;
}

export interface TransactionDirective extends BaseDirective {
  type: "transaction";
  flag: string;
  payee?: string;
  narration?: string;
  tags?: string[];
  links?: string[];
  postings: Posting[];
}

export interface OpenDirective extends BaseDirective {
  type: "open";
  account: string;
  currencies?: string[];
  booking?: string;
}

export interface CloseDirective extends BaseDirective {
  type: "close";
  account: string;
}

export interface BalanceDirective extends BaseDirective {
  type: "balance";
  account: string;
  amount: Amount;
}

export interface CommodityDirective extends BaseDirective {
  type: "commodity";
  currency: string;
}

export interface PriceDirective extends BaseDirective {
  type: "price";
  currency: string;
  amount: Amount;
}

export interface EventDirective extends BaseDirective {
  type: "event";
  event_type: string;
  value: string;
}

export interface NoteDirective extends BaseDirective {
  type: "note";
  account: string;
  comment: string;
}

export interface DocumentDirective extends BaseDirective {
  type: "document";
  account: string;
  path: string;
}

export interface PadDirective extends BaseDirective {
  type: "pad";
  account: string;
  source_account: string;
}

export interface QueryDirective extends BaseDirective {
  type: "query";
  name: string;
  query_string: string;
}

export interface CustomDirective extends BaseDirective {
  type: "custom";
  custom_type: string;
}

export type Directive =
  | TransactionDirective
  | OpenDirective
  | CloseDirective
  | BalanceDirective
  | CommodityDirective
  | PriceDirective
  | EventDirective
  | NoteDirective
  | DocumentDirective
  | PadDirective
  | QueryDirective
  | CustomDirective;

export interface DocumentSymbol {
  name: string;
  kind: string;
  detail?: string;
  range: {
    start_line: number;
    end_line: number;
    start_character: number;
    end_character: number;
  };
}

/**
 * The parts of a diagnostic this package reads.
 *
 * Deliberately a permissive INPUT shape rather than a copy of
 * `@rustledger/wasm`'s `BeancountError`. It was a copy, and it drifted: the
 * wasm type gained `file` and declares `line` as `number | null`, so passing a
 * real result into these formatters stopped type-checking, and the formatter
 * that wanted to name the file could not read the field.
 *
 * Widening instead of re-exporting keeps two things true at once — a wasm
 * result is assignable here (required properties satisfy optional ones), and a
 * test fixture can supply only the fields under test. What it must NOT do is
 * narrow: `number | null` has to stay, or the next field the wasm adds breaks
 * the build again.
 */
export interface BeancountError {
  message: string;
  severity: "error" | "warning";
  file?: string | null;
  line?: number | null;
  column?: number | null;
}

export interface QueryResult {
  columns: string[];
  rows: unknown[][];
  errors?: BeancountError[];
}

/** A validation outcome, as the wasm entry points return one. */
export interface ValidationOutcome {
  valid: boolean;
  errors: BeancountError[];
}

export interface ValidationResult {
  valid: boolean;
  errors: BeancountError[];
}

export interface FormatResult {
  formatted?: string;
  errors?: BeancountError[];
}

export interface ParseResult {
  ledger?: {
    directives: Directive[];
  };
  errors?: BeancountError[];
}

export interface ToolResponse {
  isError?: boolean;
  content: Array<{ type: "text"; text: string }>;
  [key: string]: unknown;
}

export interface ToolArguments {
  source?: string;
  query?: string;
  partial_query?: string;
  cursor_pos?: number;
  plugin_name?: string;
  line?: number;
  character?: number;
  account?: string;
  payee?: string;
  narration?: string;
  tag?: string;
  from_date?: string;
  to_date?: string;
  limit?: number;
  report_type?: string;
  currency?: string;
  file_path?: string;
  write?: boolean;
  // Used by handleImportCategorize (src/handlers.ts:107).
  amount?: string;
  date?: string;
}
