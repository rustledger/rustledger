// Helper functions for the MCP server

import * as fs from "fs";
import * as path from "path";
import type {
  BeancountError,
  ValidationOutcome,
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
 * Resolve one `include` target to the absolute paths it names.
 *
 * `include "journals/*.beancount"` is how a ledger split into monthly files is
 * normally written, and both `rledger check` and bean-check expand it. Both
 * traversers here used to hand the pattern to `path.resolve` as a literal
 * filename and fail with `ENOENT ... 'journals/*.beancount'` on a ledger the
 * CLI loads without complaint — so this lives in one place and both use it.
 *
 * Matches are sorted so the assembled source is stable run to run
 * (`fs.globSync` gives no ordering guarantee), directories are dropped since
 * only files can be included, and a pattern matching nothing is an error with
 * the wording both reference tools use.
 */
function resolveIncludeTargets(includePath: string, baseDir: string): string[] {
  if (!GLOB_CHARS.test(includePath)) {
    return [path.resolve(baseDir, includePath)];
  }

  const matches = fs
    .globSync(includePath, { cwd: baseDir })
    .map((m) => path.resolve(baseDir, m))
    .filter((m) => {
      try {
        return fs.statSync(m).isFile();
      } catch {
        return false;
      }
    })
    .sort();
  if (matches.length === 0) {
    throw new Error(`include pattern "${includePath}" does not match any files`);
  }
  return matches;
}
/**
 * Gather a ledger's files into the `{ path: contents }` map the wasm
 * multi-file entry points take, keyed relative to the entry point's directory.
 *
 * This is DISCOVERY ONLY. Include *semantics* — resolution order, glob
 * expansion, de-duplicating a file reached twice, cycle detection, and above
 * all which file and line an error belongs to — are the loader's, reached
 * through `validateMultiFile` / `queryMultiFile`, which run the same
 * `Loader` as `rledger check` over a `VirtualFileSystem` built from this map.
 *
 * That division is the point. The alternative this replaces concatenated every
 * included file into one string and validated that, which meant reimplementing
 * the loader's include handling in TypeScript — and getting it wrong four
 * separate ways (doubled diamonds, unreported duplicates, no glob support, and
 * the same gaps again in the sibling traverser). It also destroyed error
 * locations: an error on line 2 of `j/2020-07.beancount` was reported as
 * `file: null, line: 9`, a position in the concatenation that exists in none
 * of the user's files.
 *
 * Being approximate here is safe in a way that being approximate about
 * semantics is not. Over-collecting is harmless — the loader simply never
 * visits a file nothing includes. Under-collecting is reported properly, as a
 * missing include, against the file that asked for it.
 */
export function collectLedgerFiles(entryPath: string): {
  files: Record<string, string>;
  entry: string;
} {
  // Canonicalize the ENTRY before anything derives from it. Its directory
  // becomes the root every key is relative to, and a relative include inside a
  // file resolves against the directory that file really lives in — which for
  // a symlinked entry point is the target's directory, not the link's. Reading
  // through the link and then resolving `include "x.beancount"` beside the
  // LINK looked for a file that is not there, so the whole ledger failed with
  // `file not found` on a tree `rledger check` reads without trouble.
  const linkedEntry = path.resolve(entryPath);
  let absoluteEntry: string;
  try {
    absoluteEntry = fs.realpathSync(linkedEntry);
  } catch {
    absoluteEntry = linkedEntry;
  }
  const rootDir = path.dirname(absoluteEntry);
  const files: Record<string, string> = {};
  const seen = new Set<string>();

  const key = (abs: string): string =>
    path.relative(rootDir, abs).split(path.sep).join("/");

  // Canonical path -> the key it was first collected under. `path.resolve`
  // normalizes `.` and `..` but NOT symlinks, so without this a file reached
  // both directly and through a symlink lands under two keys — and a
  // VirtualFileSystem has no notion of symlinks to collapse them again, so the
  // loader would read the same directives twice and silently double every
  // amount in that file. `rledger check` resolves the link, loads it once, and
  // reports the duplicate.
  const canonical = new Map<string, string>();

  const visit = (abs: string): void => {
    if (seen.has(abs)) return;
    seen.add(abs);

    let real: string;
    try {
      real = fs.realpathSync(abs);
    } catch {
      real = abs;
    }

    const firstKey = canonical.get(real);
    if (firstKey !== undefined) {
      // An alias for a file already in the map. It still has to RESOLVE — the
      // include names this path — so stand in a one-line include of the
      // canonical copy rather than the contents. The loader then reaches the
      // same file twice and says so, which is what the CLI does, instead of
      // counting it twice.
      const target = path
        .relative(path.dirname(abs), path.resolve(rootDir, firstKey))
        .split(path.sep)
        .join("/");
      files[key(abs)] = `include "${target}"\n`;
      return;
    }

    let content: string;
    try {
      content = fs.readFileSync(abs, "utf-8");
    } catch {
      // Leave it out and let the loader report the missing include against
      // whichever file asked for it — better placed than anything we could say.
      return;
    }
    canonical.set(real, key(abs));
    files[key(abs)] = content;

    const baseDir = path.dirname(abs);
    // Fresh regex per call: a shared global one carries `lastIndex` across
    // recursive invocations.
    const includeRe = new RegExp(INCLUDE_PATTERN, "gm");
    for (const match of content.matchAll(includeRe)) {
      let targets: string[];
      try {
        targets = resolveIncludeTargets(match[1], baseDir);
      } catch {
        // A pattern matching nothing is the loader's to report.
        continue;
      }
      for (const target of targets) visit(target);
    }
  };

  visit(absoluteEntry);
  return { files, entry: key(absoluteEntry) };
}

/*
 * `loadWithIncludes` / `loadFileRecursive` used to live here: they
 * concatenated a ledger's included files into one string for validation and
 * querying. They are gone deliberately. That approach reimplemented the
 * loader's include handling in TypeScript — getting diamonds, duplicate
 * reporting, globs and directory matches wrong in turn — and, because the
 * result was one anonymous buffer, reported an error on line 2 of an included
 * file as `file: null, line: 9`.
 *
 * `collectLedgerFiles` above gathers the same files into the map the wasm
 * multi-file entry points take, and the loader does the resolving. Keeping a
 * concatenating entry point around would just be somewhere to reintroduce all
 * of it.
 *
 * `withIncludedContext` below still concatenates, correctly: the editor tools
 * need ONE buffer with the user's unsaved document first so a cursor offset
 * still resolves against it, and they report no file-attributed diagnostics.
 */

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
    // Glob-aware, the same way `collectLedgerFiles` is and through the same
    // resolver: an aggregate lookup over a ledger written as
    // `include "journals/*.beancount"` used to throw ENOENT on the pattern and
    // take hover and completions down with it.
    let targets: string[];
    try {
      targets = resolveIncludeTargets(match[1], baseDir);
    } catch (error) {
      const msg = error instanceof Error ? error.message : String(error);
      throw new Error(`Failed to include "${match[1]}": ${msg}`);
    }

    for (const includeAbsPath of targets) {
      // A single global `visited` set, added to BEFORE recursing, both
      // de-duplicates a diamond graph (a shared file is appended once, which
      // is what aggregate counts want) and makes a cycle (A -> B -> A)
      // terminate without re-appending.
      //
      // Terminating quietly is the whole behavior here, deliberately. Unlike
      // the validation path there is no loader behind this to report the
      // cycle — this assembles one buffer for hover and completions, which
      // should keep working on a ledger that has a cycle elsewhere rather
      // than failing the tool outright.
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
      // Name the file when the loader knows it. On a ledger split across
      // monthly journals a bare `:561` is close to useless — 561 of which
      // file? The multi-file entry points attribute each error to the file it
      // is actually in, so say so.
      const where = [e.file, e.line, e.line ? e.column : undefined]
        .filter((part) => part !== null && part !== undefined && part !== "")
        .join(":");
      return where ? `[${e.severity}] ${where}: ${e.message}` : `[${e.severity}] ${e.message}`;
    })
    .join("\n");
}

/**
 * The diagnostics that make a result unusable.
 *
 * A warning does not. The wasm entry points carry non-fatal notices in the
 * same `errors` array as real failures — `query` documents that it passes
 * "load warnings through every result path so callers still see them" — so a
 * bare `errors.length > 0` treats a plugin notice as a hard failure. That is
 * how a `query` on a ledger with an `unrealized` plugin returned the warning
 * and THREW AWAY the rows, where `rledger query` prints them.
 */
export function fatalErrors(errors?: BeancountError[]): BeancountError[] {
  return (errors ?? []).filter((e) => e.severity === "error");
}

/**
 * Render a validation result the way `rledger check` reports one.
 *
 * Warnings are NOT errors — a warning-only ledger is valid and the CLI exits 0
 * — but they still have to be shown. Reporting only when `valid` is false
 * meant a ledger the CLI describes as `⚠ 1 warning` came back as a bare
 * "Ledger is valid.", with the tool's own description promising "validation
 * errors and warnings".
 */
export function formatValidation(result: ValidationOutcome, prefix = ""): string {
  const head = prefix ? `${prefix}: ` : "";
  const warnings = result.errors.filter((e) => e.severity === "warning");

  if (!result.valid) {
    const errorCount = result.errors.length - warnings.length;
    return `${head}Found ${errorCount} error(s):\n${formatErrors(result.errors)}`;
  }
  if (warnings.length > 0) {
    return `${head}Ledger is valid, with ${warnings.length} warning(s):\n${formatErrors(warnings)}`;
  }
  return `${head}Ledger is valid.`;
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
