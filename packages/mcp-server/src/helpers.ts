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

/** Glob metacharacters beancount honors in an `include`. */
const GLOB_CHARS = /[*?[\]]/;

/**
 * Resolve one `include` target, which may be a glob.
 *
 * `include "journals/*.beancount"` is how a ledger split into monthly files is
 * normally written, and both `rledger check` and bean-check expand it. This
 * loader treated the pattern as a literal filename, so every file tool here
 * failed with `ENOENT ... 'journals/*.beancount'` on a ledger the CLI loads
 * without complaint.
 *
 * Matches are sorted so the assembled source is stable run to run —
 * `fs.globSync` gives no ordering guarantee — and a pattern matching nothing
 * is an error, with the wording both reference tools use.
 */
function expandInclude(
  includePath: string,
  baseDir: string,
  stack: Set<string>,
  emitted: Set<string>,
  duplicates: string[]
): string {
  if (!GLOB_CHARS.test(includePath)) {
    return loadFileRecursive(
      path.resolve(baseDir, includePath),
      stack,
      emitted,
      duplicates
    );
  }

  const matches = fs
    .globSync(includePath, { cwd: baseDir })
    .map((m) => path.resolve(baseDir, m))
    .sort();
  if (matches.length === 0) {
    throw new Error(`include pattern "${includePath}" does not match any files`);
  }
  return matches
    .map((m) => loadFileRecursive(m, stack, emitted, duplicates))
    .join("\n");
}

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
  return loadWithIncludesDetailed(filePath).source;
}

/**
 * As [`loadWithIncludes`], but also reports files reached more than once.
 *
 * `rledger check` and bean-check both treat a duplicate include as an ERROR
 * (`Duplicate filename parsed`, exit 1) while still loading the file once.
 * De-duplicating silently here would load the right ledger but call it clean,
 * which is the same disagreement with the CLI — just quieter — as inlining it
 * twice was.
 */
export function loadWithIncludesDetailed(filePath: string): {
  source: string;
  duplicates: string[];
} {
  const duplicates: string[] = [];
  const source = loadFileRecursive(
    filePath,
    new Set<string>(),
    new Set<string>(),
    duplicates
  );
  return { source, duplicates };
}

/**
 * @param stack  files on the current recursion path — a repeat is a CYCLE.
 * @param emitted  every file already inlined anywhere in this load — a repeat
 *   is a DIAMOND, and must contribute its directives only once.
 *
 * The two sets answer different questions and both are needed. `stack` alone
 * (which is what this used to carry, deleting on the way out "to allow same
 * file from different branches") lets a diamond through: include `x` directly
 * and again via a file that includes it, and every transaction in `x` lands in
 * the source twice. Nothing then errors — the ledger simply has doubled
 * amounts, so balances are wrong and assertions fail against figures the user
 * cannot find. Sharing a `prices` or `accounts` file between monthly journals
 * is an ordinary way to reach that.
 *
 * `rledger check` and bean-check both parse such a file once (beancount also
 * says `Duplicate filename parsed`), so inlining it twice made this tool
 * disagree with the CLI it is meant to mirror.
 *
 * A cycle still throws, which is what the CLI does with one too — see the
 * ordering note in the body, which is what makes that true.
 */
function loadFileRecursive(
  filePath: string,
  stack: Set<string>,
  emitted: Set<string>,
  duplicates: string[]
): string {
  const absolutePath = path.resolve(filePath);

  // Order matters. A file on the current path is a CYCLE and must throw, the
  // way `rledger check` errors on one; a file merely seen before is a DIAMOND
  // and is skipped. Testing `emitted` first turns the former into the latter,
  // because a cycle's repeat is always also a repeat — and the tool then
  // reports a ledger clean that the CLI refuses.
  if (stack.has(absolutePath)) {
    throw new Error(`Circular include detected: ${absolutePath}`);
  }
  if (emitted.has(absolutePath)) {
    duplicates.push(absolutePath);
    return "";
  }
  stack.add(absolutePath);
  emitted.add(absolutePath);

  try {
    const source = fs.readFileSync(absolutePath, "utf-8");
    const baseDir = path.dirname(absolutePath);

    // Replace each include directive with the contents of the included file
    return source.replace(INCLUDE_REGEX, (_match, includePath: string) => {
      try {
        return expandInclude(includePath, baseDir, stack, emitted, duplicates);
      } catch (error) {
        // Re-throw with context about which include failed
        const msg = error instanceof Error ? error.message : String(error);
        throw new Error(`Failed to include "${includePath}" from ${absolutePath}: ${msg}`);
      }
    });
  } finally {
    // Leave the recursion path; `emitted` deliberately persists for the load.
    stack.delete(absolutePath);
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
