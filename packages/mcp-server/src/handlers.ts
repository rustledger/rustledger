// Tool handlers for the MCP server

import * as fs from "fs";
import * as path from "path";
import * as rustledger from "@rustledger/wasm";
import type {
  Directive,
  DocumentSymbol,
  ToolResponse,
  ToolArguments,
} from "./types.js";
import {
  validateArgs,
  errorResponse,
  textResponse,
  jsonResponse,
  formatErrors,
  formatQueryResult,
  loadWithIncludes,
  withIncludedContext,
} from "./helpers.js";
import { getBqlTablesDocs } from "./resources.js";

/**
 * Handle a tool call and return the response.
 */
export function handleToolCall(
  name: string,
  args: ToolArguments | undefined
): ToolResponse {
  switch (name) {
    // === Original Tools ===
    case "validate":
      return handleValidate(args);
    case "query":
      return handleQuery(args);
    case "balances":
      return handleBalances(args);
    case "format":
      return handleFormat(args);
    case "parse":
      return handleParse(args);
    case "completions":
      return handleCompletions(args);
    case "list_plugins":
      return handleListPlugins();
    case "run_plugin":
      return handleRunPlugin(args);

    // === Editor Tools ===
    case "editor_completions":
      return handleEditorCompletions(args);
    case "editor_hover":
      return handleEditorHover(args);
    case "editor_definition":
      return handleEditorDefinition(args);
    case "editor_document_symbols":
      return handleEditorDocumentSymbols(args);
    case "editor_references":
      return handleEditorReferences(args);

    // === Analysis Tools ===
    case "ledger_stats":
      return handleLedgerStats(args);
    case "list_accounts":
      return handleListAccounts(args);
    case "list_commodities":
      return handleListCommodities(args);
    case "account_activity":
      return handleAccountActivity(args);

    // === Utility Tools ===
    case "format_check":
      return handleFormatCheck(args);
    case "bql_tables":
      return handleBqlTables();
    case "directive_at_line":
      return handleDirectiveAtLine(args);
    case "find_transactions":
      return handleFindTransactions(args);

    // === Report Tool ===
    case "report":
      return handleReport(args);

    // === File Operation Tools ===
    case "validate_file":
      return handleValidateFile(args);
    case "query_file":
      return handleQueryFile(args);
    case "format_file":
      return handleFormatFile(args);

    // === Import Tools ===
    case "import_categorize":
      return handleImportCategorize(args);
    case "import_review":
      return handleImportReview(args);

    default:
      return errorResponse(`Unknown tool: ${name}`);
  }
}

// === Import Tools ===

function handleImportCategorize(
  args: ToolArguments | undefined
): ToolResponse {
  const validation = validateArgs(args, ["source", "narration", "date"]);
  if (validation) return validation;

  try {
    const source = args!.source as string;
    // `rustledger.parse()` returns the `ParseResult` object directly
    // (via `serde_wasm_bindgen::Serializer::json_compatible()` -- no
    // intermediate JSON string). Pre-#1227 this called `JSON.parse(result)`,
    // which threw at runtime because the value was already an object.
    const result = rustledger.parse(source);
    if (result.errors?.length > 0) {
      return errorResponse(formatErrors(result.errors));
    }
    const directives = result.ledger?.directives ?? [];

    // Extract expense/income accounts from the ledger
    const accounts = new Set<string>();
    for (const d of directives) {
      if (d.type === "open" && d.account) {
        if (
          d.account.startsWith("Expenses:") ||
          d.account.startsWith("Income:")
        ) {
          accounts.add(d.account);
        }
      }
      if (d.type === "transaction" && d.postings) {
        for (const p of d.postings) {
          if (
            p.account.startsWith("Expenses:") ||
            p.account.startsWith("Income:")
          ) {
            accounts.add(p.account);
          }
        }
      }
    }

    const sortedAccounts = Array.from(accounts).sort();
    const payee = (args!.payee as string) || undefined;
    const narration = args!.narration as string;
    const amount = (args!.amount as string) || undefined;
    const currency = (args!.currency as string) || "USD";
    const date = args!.date as string;

    // Build a categorization prompt
    let prompt = "Categorize this financial transaction into the most appropriate account.\n\n";
    prompt += "Transaction:\n";
    prompt += `  Date: ${date}\n`;
    if (payee) prompt += `  Payee: ${payee}\n`;
    prompt += `  Description: ${narration}\n`;
    if (amount) prompt += `  Amount: ${amount} ${currency}\n`;
    prompt += "\nAvailable accounts:\n";
    for (const acct of sortedAccounts) {
      prompt += `  - ${acct}\n`;
    }
    prompt += "\nRespond with ONLY the account name on the first line, ";
    prompt += "followed by a brief reason on the second line.\n";

    return jsonResponse({
      prompt,
      known_accounts: sortedAccounts,
      transaction: { payee, narration, amount, currency, date },
    });
  } catch (error) {
    return errorResponse(
      `Failed to build categorization prompt: ${error instanceof Error ? error.message : String(error)}`
    );
  }
}

function handleImportReview(args: ToolArguments | undefined): ToolResponse {
  const validation = validateArgs(args, ["source"]);
  if (validation) return validation;

  try {
    const source = args!.source as string;
    // See `handleImportCategorize` (above) for the parse-result shape
    // notes; same fix as in #1227.
    const result = rustledger.parse(source);
    if (result.errors?.length > 0) {
      return errorResponse(formatErrors(result.errors));
    }
    const directives = result.ledger?.directives ?? [];

    const needsReview: Array<{
      date: string;
      narration: string;
      payee?: string;
      account: string;
      confidence: number;
      method: string;
    }> = [];

    for (const d of directives) {
      if (d.type === "transaction" && d.meta) {
        const confidence = d.meta["import-confidence"];
        if (confidence !== undefined) {
          const method = d.meta["import-method"] || "unknown";
          const account =
            d.postings && d.postings.length > 1
              ? d.postings[1].account
              : "unknown";
          needsReview.push({
            date: d.date,
            narration: d.narration || "",
            payee: d.payee || undefined,
            account,
            confidence: Number(confidence),
            method: String(method),
          });
        }
      }
    }

    const high = needsReview.filter((t) => t.confidence > 0.9);
    const medium = needsReview.filter(
      (t) => t.confidence >= 0.5 && t.confidence <= 0.9
    );
    const low = needsReview.filter((t) => t.confidence < 0.5);

    return jsonResponse({
      total: needsReview.length,
      high_confidence: high.length,
      medium_confidence: medium.length,
      low_confidence: low.length,
      needs_review: [...low, ...medium],
      accepted: high,
    });
  } catch (error) {
    return errorResponse(
      `Failed to review imports: ${error instanceof Error ? error.message : String(error)}`
    );
  }
}

// === Original Tools ===

function handleValidate(args: ToolArguments | undefined): ToolResponse {
  const validation = validateArgs(args, ["source"]);
  if (validation) return validation;

  const source = args!.source!;
  const result = rustledger.validateSource(source);
  return textResponse(
    result.valid
      ? "Ledger is valid."
      : `Found ${result.errors.length} error(s):\n${formatErrors(result.errors)}`
  );
}

function handleQuery(args: ToolArguments | undefined): ToolResponse {
  const validation = validateArgs(args, ["source", "query"]);
  if (validation) return validation;

  const result = rustledger.query(args!.source!, args!.query!);
  if (result.errors?.length > 0) {
    return errorResponse(formatErrors(result.errors));
  }
  return textResponse(formatQueryResult(result));
}

function handleBalances(args: ToolArguments | undefined): ToolResponse {
  const validation = validateArgs(args, ["source"]);
  if (validation) return validation;

  const result = rustledger.balances(args!.source!);
  if (result.errors?.length > 0) {
    return errorResponse(formatErrors(result.errors));
  }
  return textResponse(formatQueryResult(result));
}

function handleFormat(args: ToolArguments | undefined): ToolResponse {
  const validation = validateArgs(args, ["source"]);
  if (validation) return validation;

  const result = rustledger.format(args!.source!);
  if (result.errors?.length > 0) {
    return errorResponse(formatErrors(result.errors));
  }
  return textResponse(result.formatted || "");
}

function handleParse(args: ToolArguments | undefined): ToolResponse {
  const validation = validateArgs(args, ["source"]);
  if (validation) return validation;

  const result = rustledger.parse(args!.source!);
  if (result.errors?.length > 0) {
    return errorResponse(formatErrors(result.errors));
  }
  return jsonResponse(result.ledger);
}

function handleCompletions(args: ToolArguments | undefined): ToolResponse {
  const validation = validateArgs(args, ["partial_query", "cursor_pos"]);
  if (validation) return validation;

  const result = rustledger.bqlCompletions(args!.partial_query!, args!.cursor_pos!);
  return jsonResponse(result);
}

function handleListPlugins(): ToolResponse {
  const plugins = rustledger.listPlugins();
  return jsonResponse(plugins);
}

function handleRunPlugin(args: ToolArguments | undefined): ToolResponse {
  const validation = validateArgs(args, ["source", "plugin_name"]);
  if (validation) return validation;

  const result = rustledger.runPlugin(args!.source!, args!.plugin_name!);
  if (result.errors?.length > 0) {
    return errorResponse(formatErrors(result.errors));
  }
  return textResponse(`Plugin processed ${result.directives.length} directives.`);
}

// === Editor Tools ===

/**
 * Resolve the source an editor tool should operate on.
 *
 * Accepts inline `source`, a `file_path` to read from disk, or both (then
 * `source` is the unsaved-buffer content and wins, while `file_path` still
 * anchors include resolution). Returns either the resolved source string or a
 * ToolResponse describing the error (neither input given, or a read failure).
 *
 * When `withContext` is true and a `file_path` is given, the edited document
 * is augmented with the contents of every file it `include`s (appended after
 * it, so cursor coordinates are preserved) — giving hover/completions
 * whole-ledger balances and account names. Location-returning tools
 * (definition/references) and the document outline pass `withContext: false`
 * and operate on the edited document alone.
 */
type ResolvedEditorSource =
  | { ok: true; source: string }
  | { ok: false; response: ToolResponse };

function resolveEditorSource(
  args: ToolArguments | undefined,
  withContext: boolean
): ResolvedEditorSource {
  const inlineSource = args?.source;
  const filePath = args?.file_path;

  if (inlineSource == null && filePath == null) {
    return {
      ok: false,
      response: errorResponse(
        "Provide either 'source' (inline ledger text) or 'file_path' (a ledger file to read)."
      ),
    };
  }
  if (filePath == null) {
    return { ok: true, source: inlineSource! };
  }

  try {
    const absolutePath = path.resolve(filePath);
    const baseDir = path.dirname(absolutePath);
    // `source` (an unsaved buffer) overrides the on-disk contents; `file_path`
    // still anchors include resolution.
    const editedSource = inlineSource ?? fs.readFileSync(absolutePath, "utf-8");
    return {
      ok: true,
      source: withContext
        ? withIncludedContext(editedSource, baseDir)
        : editedSource,
    };
  } catch (error) {
    return {
      ok: false,
      response: errorResponse(
        `Error reading file: ${error instanceof Error ? error.message : String(error)}`
      ),
    };
  }
}

function handleEditorCompletions(args: ToolArguments | undefined): ToolResponse {
  const validation = validateArgs(args, ["line", "character"]);
  if (validation) return validation;

  // Whole-ledger context so completions can offer accounts/commodities
  // defined in included files (#1328, #1297).
  const resolved = resolveEditorSource(args, true);
  if (!resolved.ok) return resolved.response;

  const ledger = new rustledger.ParsedLedger(resolved.source);
  const result = ledger.getCompletions(args!.line!, args!.character!);
  ledger.free();
  return jsonResponse(result);
}

function handleEditorHover(args: ToolArguments | undefined): ToolResponse {
  const validation = validateArgs(args, ["line", "character"]);
  if (validation) return validation;

  // Whole-ledger context so the hovered account's balance and transaction
  // count reflect the full ledger, not just the edited file (#1328).
  const resolved = resolveEditorSource(args, true);
  if (!resolved.ok) return resolved.response;

  const ledger = new rustledger.ParsedLedger(resolved.source);
  const result = ledger.getHoverInfo(args!.line!, args!.character!);
  ledger.free();

  if (!result) {
    return textResponse("No hover information available at this position.");
  }
  return jsonResponse(result);
}

function handleEditorDefinition(args: ToolArguments | undefined): ToolResponse {
  const validation = validateArgs(args, ["line", "character"]);
  if (validation) return validation;

  // Document-local: a definition returns a (line, character) location, which
  // would be meaningless in the synthetic whole-ledger concatenation. Cross-
  // file go-to-definition is a known limitation (see helpers.withIncludedContext).
  const resolved = resolveEditorSource(args, false);
  if (!resolved.ok) return resolved.response;

  const ledger = new rustledger.ParsedLedger(resolved.source);
  const result = ledger.getDefinition(args!.line!, args!.character!);
  ledger.free();

  if (!result) {
    return textResponse("No definition found at this position.");
  }
  return jsonResponse(result);
}

function handleEditorDocumentSymbols(args: ToolArguments | undefined): ToolResponse {
  // Document outline of the edited file only — including other files' symbols
  // would pollute the outline.
  const resolved = resolveEditorSource(args, false);
  if (!resolved.ok) return resolved.response;

  const ledger = new rustledger.ParsedLedger(resolved.source);
  const result = ledger.getDocumentSymbols();
  ledger.free();
  return jsonResponse(result);
}

function handleEditorReferences(args: ToolArguments | undefined): ToolResponse {
  const validation = validateArgs(args, ["line", "character"]);
  if (validation) return validation;

  // Document-local, same rationale as editor_definition: references return
  // locations that only make sense within the edited file's coordinate space.
  const resolved = resolveEditorSource(args, false);
  if (!resolved.ok) return resolved.response;

  const ledger = new rustledger.ParsedLedger(resolved.source);
  const result = ledger.getReferences(args!.line!, args!.character!);
  ledger.free();

  if (!result) {
    return textResponse("No references found at this position.");
  }
  return jsonResponse(result);
}

// === Analysis Tools ===

function handleLedgerStats(args: ToolArguments | undefined): ToolResponse {
  const validation = validateArgs(args, ["source"]);
  if (validation) return validation;

  const ledger = new rustledger.ParsedLedger(args!.source!);
  const directives = ledger.getDirectives();

  const stats = {
    total_directives: directives.length,
    transactions: 0,
    open_accounts: 0,
    close_accounts: 0,
    balance_assertions: 0,
    commodities: 0,
    prices: 0,
    events: 0,
    notes: 0,
    documents: 0,
    pads: 0,
    queries: 0,
    custom: 0,
    unique_accounts: new Set<string>(),
    unique_currencies: new Set<string>(),
    date_range: { first: "", last: "" },
    is_valid: ledger.isValid(),
    error_count: ledger.getErrors().length,
  };

  for (const d of directives as Directive[]) {
    if (!stats.date_range.first || d.date < stats.date_range.first) {
      stats.date_range.first = d.date;
    }
    if (!stats.date_range.last || d.date > stats.date_range.last) {
      stats.date_range.last = d.date;
    }

    switch (d.type) {
      case "transaction":
        stats.transactions++;
        for (const p of d.postings) {
          stats.unique_accounts.add(p.account);
          if (p.units?.currency) {
            stats.unique_currencies.add(p.units.currency);
          }
        }
        break;
      case "open":
        stats.open_accounts++;
        stats.unique_accounts.add(d.account);
        break;
      case "close":
        stats.close_accounts++;
        break;
      case "balance":
        stats.balance_assertions++;
        break;
      case "commodity":
        stats.commodities++;
        stats.unique_currencies.add(d.currency);
        break;
      case "price":
        stats.prices++;
        break;
      case "event":
        stats.events++;
        break;
      case "note":
        stats.notes++;
        break;
      case "document":
        stats.documents++;
        break;
      case "pad":
        stats.pads++;
        break;
      case "query":
        stats.queries++;
        break;
      case "custom":
        stats.custom++;
        break;
    }
  }

  ledger.free();

  // Destructure to exclude Set fields, then build clean output
  const { unique_accounts, unique_currencies, ...baseStats } = stats;
  const output = {
    ...baseStats,
    account_count: unique_accounts.size,
    currency_count: unique_currencies.size,
    currencies: Array.from(unique_currencies),
  };

  return jsonResponse(output);
}

function handleListAccounts(args: ToolArguments | undefined): ToolResponse {
  const validation = validateArgs(args, ["source"]);
  if (validation) return validation;

  const ledger = new rustledger.ParsedLedger(args!.source!);
  const directives = ledger.getDirectives();

  const accounts: Record<
    string,
    { open_date?: string; close_date?: string; currencies: string[]; booking?: string }
  > = {};

  for (const d of directives as Directive[]) {
    if (d.type === "open") {
      accounts[d.account] = {
        open_date: d.date,
        currencies: d.currencies || [],
        booking: d.booking,
      };
    } else if (d.type === "close") {
      if (accounts[d.account]) {
        accounts[d.account].close_date = d.date;
      } else {
        accounts[d.account] = { close_date: d.date, currencies: [] };
      }
    }
  }

  ledger.free();
  return jsonResponse(accounts);
}

function handleListCommodities(args: ToolArguments | undefined): ToolResponse {
  const validation = validateArgs(args, ["source"]);
  if (validation) return validation;

  const ledger = new rustledger.ParsedLedger(args!.source!);
  const directives = ledger.getDirectives();

  const commodities = new Set<string>();

  for (const d of directives as Directive[]) {
    if (d.type === "commodity") {
      commodities.add(d.currency);
    } else if (d.type === "price") {
      commodities.add(d.currency);
      commodities.add(d.amount.currency);
    } else if (d.type === "transaction") {
      for (const p of d.postings) {
        if (p.units?.currency) {
          commodities.add(p.units.currency);
        }
      }
    }
  }

  ledger.free();
  return jsonResponse(Array.from(commodities).sort());
}

function handleAccountActivity(args: ToolArguments | undefined): ToolResponse {
  const validation = validateArgs(args, ["source", "account"]);
  if (validation) return validation;

  const account = args!.account!;
  const ledger = new rustledger.ParsedLedger(args!.source!);
  const directives = ledger.getDirectives();

  const activity = {
    account,
    open_date: null as string | null,
    close_date: null as string | null,
    first_transaction: null as string | null,
    last_transaction: null as string | null,
    transaction_count: 0,
    currencies_used: new Set<string>(),
  };

  for (const d of directives as Directive[]) {
    if (d.type === "open" && d.account === account) {
      activity.open_date = d.date;
    } else if (d.type === "close" && d.account === account) {
      activity.close_date = d.date;
    } else if (d.type === "transaction") {
      for (const p of d.postings) {
        if (p.account === account || p.account.startsWith(account + ":")) {
          activity.transaction_count++;
          if (!activity.first_transaction || d.date < activity.first_transaction) {
            activity.first_transaction = d.date;
          }
          if (!activity.last_transaction || d.date > activity.last_transaction) {
            activity.last_transaction = d.date;
          }
          if (p.units?.currency) {
            activity.currencies_used.add(p.units.currency);
          }
          break;
        }
      }
    }
  }

  ledger.free();

  return jsonResponse({
    ...activity,
    currencies_used: Array.from(activity.currencies_used),
  });
}

// === Utility Tools ===

function handleFormatCheck(args: ToolArguments | undefined): ToolResponse {
  const validation = validateArgs(args, ["source"]);
  if (validation) return validation;

  const source = args!.source!;
  const result = rustledger.format(source);
  if (result.errors?.length > 0) {
    return errorResponse(formatErrors(result.errors));
  }
  const formatted = result.formatted || "";
  const isFormatted = source === formatted;
  const lineDifference = Math.abs(formatted.split("\n").length - source.split("\n").length);
  return textResponse(
    isFormatted
      ? "File is properly formatted."
      : `File needs formatting. ${lineDifference} line(s) would change.`
  );
}

function handleBqlTables(): ToolResponse {
  return textResponse(getBqlTablesDocs());
}

function handleDirectiveAtLine(args: ToolArguments | undefined): ToolResponse {
  const validation = validateArgs(args, ["source", "line"]);
  if (validation) return validation;

  const line = args!.line!;
  const ledger = new rustledger.ParsedLedger(args!.source!);
  const symbols = ledger.getDocumentSymbols();
  ledger.free();

  // Find the symbol that contains this line
  for (const symbol of symbols as DocumentSymbol[]) {
    if (symbol.range.start_line <= line - 1 && symbol.range.end_line >= line - 1) {
      return jsonResponse(symbol);
    }
  }

  return textResponse("No directive found at this line.");
}

function handleFindTransactions(args: ToolArguments | undefined): ToolResponse {
  const validation = validateArgs(args, ["source"]);
  if (validation) return validation;

  const payee = args?.payee;
  const narration = args?.narration;
  const tag = args?.tag;
  const fromDate = args?.from_date;
  const toDate = args?.to_date;
  const limit = args?.limit || 50;

  const ledger = new rustledger.ParsedLedger(args!.source!);
  const directives = ledger.getDirectives();
  ledger.free();

  const results: unknown[] = [];

  for (const d of directives as Directive[]) {
    if (results.length >= limit) break;
    if (d.type !== "transaction") continue;

    if (fromDate && d.date < fromDate) continue;
    if (toDate && d.date > toDate) continue;
    if (payee && (!d.payee || !d.payee.toLowerCase().includes(payee.toLowerCase())))
      continue;
    if (
      narration &&
      (!d.narration || !d.narration.toLowerCase().includes(narration.toLowerCase()))
    )
      continue;
    if (tag && (!d.tags || !d.tags.includes(tag))) continue;

    results.push(d);
  }

  return jsonResponse(results);
}

// === Report Tool ===

function handleReport(args: ToolArguments | undefined): ToolResponse {
  const validation = validateArgs(args, ["source", "report_type"]);
  if (validation) return validation;

  const reportType = args!.report_type!;
  let query: string;

  switch (reportType) {
    case "balsheet":
      query = `SELECT account, sum(position)
               WHERE account ~ "^(Assets|Liabilities)"
               GROUP BY account
               ORDER BY account`;
      break;
    case "income":
      query = `SELECT account, sum(position)
               WHERE account ~ "^(Income|Expenses)"
               GROUP BY account
               ORDER BY account`;
      break;
    case "balances":
      query = "BALANCES";
      break;
    case "holdings":
      query = `SELECT account, sum(position)
               WHERE account ~ "^Assets"
               GROUP BY account
               ORDER BY account`;
      break;
    case "networth":
      query = `SELECT sum(position)
               WHERE account ~ "^(Assets|Liabilities)"`;
      break;
    default:
      return errorResponse(`Unknown report type: ${reportType}`);
  }

  const result = rustledger.query(args!.source!, query);
  if (result.errors?.length > 0) {
    return errorResponse(formatErrors(result.errors));
  }

  return textResponse(`# ${reportType.toUpperCase()} Report\n\n${formatQueryResult(result)}`);
}

// === File Operation Tools ===

function handleValidateFile(args: ToolArguments | undefined): ToolResponse {
  const validation = validateArgs(args, ["file_path"]);
  if (validation) return validation;

  try {
    const absolutePath = path.resolve(args!.file_path!);
    // Load file with includes resolved
    const source = loadWithIncludes(absolutePath);
    const result = rustledger.validateSource(source);
    return textResponse(
      result.valid
        ? `${absolutePath}: Ledger is valid.`
        : `${absolutePath}: Found ${result.errors.length} error(s):\n${formatErrors(result.errors)}`
    );
  } catch (error) {
    return errorResponse(
      `Error reading file: ${error instanceof Error ? error.message : String(error)}`
    );
  }
}

function handleQueryFile(args: ToolArguments | undefined): ToolResponse {
  const validation = validateArgs(args, ["file_path", "query"]);
  if (validation) return validation;

  try {
    const absolutePath = path.resolve(args!.file_path!);
    // Load file with includes resolved
    const source = loadWithIncludes(absolutePath);
    const result = rustledger.query(source, args!.query!);
    if (result.errors?.length > 0) {
      return errorResponse(formatErrors(result.errors));
    }
    return textResponse(formatQueryResult(result));
  } catch (error) {
    return errorResponse(
      `Error: ${error instanceof Error ? error.message : String(error)}`
    );
  }
}

function handleFormatFile(args: ToolArguments | undefined): ToolResponse {
  const validation = validateArgs(args, ["file_path"]);
  if (validation) return validation;

  try {
    const absolutePath = path.resolve(args!.file_path!);
    const source = fs.readFileSync(absolutePath, "utf-8");
    const result = rustledger.format(source);
    if (result.errors?.length > 0) {
      return errorResponse(formatErrors(result.errors));
    }
    if (args?.write && result.formatted) {
      fs.writeFileSync(absolutePath, result.formatted);
      return textResponse(`Formatted and saved: ${absolutePath}`);
    }
    return textResponse(result.formatted || "");
  } catch (error) {
    return errorResponse(
      `Error: ${error instanceof Error ? error.message : String(error)}`
    );
  }
}
