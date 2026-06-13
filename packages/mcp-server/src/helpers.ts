// Helper functions for the MCP server

import * as fs from "fs";
import * as path from "path";
import type {
  BeancountError,
  QueryResult,
  ToolResponse,
  ToolArguments,
} from "./types.js";

// Source for the include-directive matcher, e.g. `include "path/file.beancount"`.
// Tolerates an optional leading BOM on the first line, and an optional trailing
// `;` comment (`include "x" ; note`) which is valid beancount the parser treats
// as trivia. `[ \t]*` before/after avoids crossing line boundaries. Callers
// that need a fresh `lastIndex` (recursion) build a new RegExp from this; the
// module-level constant is used by `.replace()`, which manages `lastIndex`.
const INCLUDE_PATTERN = '^\\uFEFF?include\\s+"([^"]+)"[ \\t]*(?:;[^\\r\\n]*)?[ \\t\\r]*$';
const INCLUDE_REGEX = new RegExp(INCLUDE_PATTERN, 'gm');

/**
 * Load a beancount file with all its includes resolved.
 *
 * This recursively follows include directives and returns the concatenated
 * source with all includes inlined. Paths in include directives are resolved
 * relative to the file containing the include.
 *
 * @param filePath - The absolute path to the main beancount file
 * @returns The concatenated source with all includes resolved
 * @throws Error if a file cannot be read or circular include detected
 */
export function loadWithIncludes(filePath: string): string {
  const visited = new Set<string>();
  return loadFileRecursive(filePath, visited);
}

function loadFileRecursive(filePath: string, visited: Set<string>): string {
  const absolutePath = path.resolve(filePath);

  // Check for circular includes (only in current recursion stack)
  if (visited.has(absolutePath)) {
    throw new Error(`Circular include detected: ${absolutePath}`);
  }
  visited.add(absolutePath);

  try {
    const source = fs.readFileSync(absolutePath, "utf-8");
    const baseDir = path.dirname(absolutePath);

    // Replace each include directive with the contents of the included file
    return source.replace(INCLUDE_REGEX, (_match, includePath: string) => {
      const includeAbsPath = path.resolve(baseDir, includePath);
      try {
        return loadFileRecursive(includeAbsPath, visited);
      } catch (error) {
        // Re-throw with context about which include failed
        const msg = error instanceof Error ? error.message : String(error);
        throw new Error(`Failed to include "${includePath}" from ${absolutePath}: ${msg}`);
      }
    });
  } finally {
    // Remove from visited after processing to allow same file from different branches
    visited.delete(absolutePath);
  }
}

/**
 * Build a whole-ledger source for the *aggregate* editor tools (hover,
 * completions) WITHOUT shifting the edited document's line numbers.
 *
 * The edited document is kept verbatim and FIRST, so a `(line, character)`
 * cursor still resolves against it. The recursively-resolved contents of
 * every file it `include`s are appended AFTER it, so balances, transaction
 * counts and candidate accounts reflect the whole ledger. Each included file
 * is appended at most once (de-duplicated across the include graph), and the
 * `include` lines in the edited document — which the parser treats as inert
 * directives — keep it from being double-counted.
 *
 * This append strategy is why these tools resolve includes while
 * `editor_definition` / `editor_references` do not: appended directives have
 * synthetic line numbers that don't map back to any real file, which is fine
 * for "what is this account's balance" but wrong for "where is it defined".
 *
 * @param editedSource - The source of the file under the cursor.
 * @param baseDir - Directory the edited document's includes resolve against
 *   (normally the directory of its `file_path`).
 * @returns `editedSource` followed by the appended include contents (or
 *   `editedSource` unchanged when it includes nothing).
 * @throws Error if an included file cannot be read.
 */
export function withIncludedContext(editedSource: string, baseDir: string): string {
  const visited = new Set<string>();
  const appended: string[] = [];
  appendIncludes(editedSource, baseDir, visited, appended);
  return appended.length === 0 ? editedSource : [editedSource, ...appended].join("\n");
}

function appendIncludes(
  source: string,
  baseDir: string,
  visited: Set<string>,
  out: string[]
): void {
  // Fresh regex per call: a shared global regex would carry `lastIndex`
  // state across recursive invocations.
  const includeRe = new RegExp(INCLUDE_PATTERN, 'gm');
  for (const match of source.matchAll(includeRe)) {
    const includeAbsPath = path.resolve(baseDir, match[1]);
    // A single global `visited` set, added to BEFORE recursing, both
    // de-duplicates a diamond graph (a shared file is appended once, which is
    // what aggregate counts want) and makes a cycle (A -> B -> A) terminate
    // without re-appending. Unlike `loadWithIncludes`, this does NOT throw on a
    // cycle: an aggregate lookup for hover/completions stays useful even if the
    // ledger has an include cycle elsewhere, rather than failing the whole tool.
    if (visited.has(includeAbsPath)) continue;
    visited.add(includeAbsPath);
    let content: string;
    try {
      content = fs.readFileSync(includeAbsPath, "utf-8");
    } catch (error) {
      const msg = error instanceof Error ? error.message : String(error);
      throw new Error(`Failed to include "${match[1]}": ${msg}`);
    }
    out.push(content);
    // Nested includes resolve relative to the included file's directory.
    appendIncludes(content, path.dirname(includeAbsPath), visited, out);
  }
}

/**
 * Validate that required arguments are present.
 * Returns a ToolResponse with error if validation fails, null otherwise.
 */
export function validateArgs(
  args: ToolArguments | undefined,
  required: (keyof ToolArguments)[]
): ToolResponse | null {
  const missing: string[] = [];

  for (const key of required) {
    const value = args?.[key];
    // Check for undefined, null, or empty string for string types
    if (value === undefined || value === null) {
      missing.push(key);
    }
  }

  if (missing.length > 0) {
    const argList = missing.join(", ");
    return {
      isError: true,
      content: [
        {
          type: "text",
          text: `Missing required argument${missing.length > 1 ? "s" : ""}: ${argList}`,
        },
      ],
    };
  }

  return null;
}

/**
 * Create an error response.
 */
export function errorResponse(message: string): ToolResponse {
  return {
    isError: true,
    content: [{ type: "text", text: message }],
  };
}

/**
 * Create a success response with text content.
 */
export function textResponse(text: string): ToolResponse {
  return {
    content: [{ type: "text", text }],
  };
}

/**
 * Create a success response with JSON content.
 */
export function jsonResponse(data: unknown): ToolResponse {
  return {
    content: [{ type: "text", text: JSON.stringify(data, null, 2) }],
  };
}

/**
 * Format validation/parse errors for display.
 */
export function formatErrors(errors: BeancountError[]): string {
  return errors
    .map((e) => {
      const loc = e.line ? `:${e.line}${e.column ? `:${e.column}` : ""}` : "";
      return `[${e.severity}]${loc} ${e.message}`;
    })
    .join("\n");
}

/**
 * Format a query result as a table.
 */
export function formatQueryResult(result: QueryResult): string {
  if (!result.columns || result.columns.length === 0) {
    return "No results.";
  }

  const { columns, rows } = result;

  // Calculate column widths
  const widths = columns.map((col, i) => {
    const maxRowWidth = Math.max(
      ...rows.map((row) => formatCell(row[i]).length)
    );
    return Math.max(col.length, maxRowWidth);
  });

  // Format header
  const header = columns.map((col, i) => col.padEnd(widths[i])).join(" | ");
  const separator = widths.map((w) => "-".repeat(w)).join("-+-");

  // Format rows
  const formattedRows = rows.map((row) =>
    row.map((cell, i) => formatCell(cell).padEnd(widths[i])).join(" | ")
  );

  return [header, separator, ...formattedRows].join("\n");
}

/**
 * Format a single cell value for display.
 */
export function formatCell(value: unknown): string {
  if (value === null || value === undefined) {
    return "";
  }
  if (typeof value === "object") {
    // Handle Amount type
    if ("number" in value && "currency" in value) {
      const amount = value as { number: string; currency: string };
      return `${amount.number} ${amount.currency}`;
    }
    // Handle Inventory type
    if ("positions" in value) {
      const inv = value as {
        positions: Array<{ units: { number: string; currency: string } }>;
      };
      return inv.positions
        .map((p) => `${p.units.number} ${p.units.currency}`)
        .join(", ");
    }
    return JSON.stringify(value);
  }
  return String(value);
}
