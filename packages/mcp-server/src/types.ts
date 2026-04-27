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

export interface BeancountError {
  message: string;
  line?: number;
  column?: number;
  severity: "error" | "warning";
}

export interface QueryResult {
  columns: string[];
  rows: unknown[][];
  errors?: BeancountError[];
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
