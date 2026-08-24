import { describe, it, expect, beforeAll, afterAll } from 'vitest';
import * as fs from 'fs';
import * as path from 'path';
import * as os from 'os';
import { fileURLToPath } from 'url';
import { initSync } from '@rustledger/wasm';
import * as rustledger from '@rustledger/wasm';
import { handleToolCall } from '../handlers.js';
import { validateArgs, formatErrors, formatValidation, fatalErrors, formatQueryResult, textResponse, errorResponse, jsonResponse, collectLedgerFiles, withIncludedContext } from '../helpers.js';
import { TOOLS } from '../tools.js';
import { RESOURCES, getResourceContents } from '../resources.js';
import { PROMPTS, getPrompt } from '../prompts.js';

// Initialize WASM before tests using synchronous initialization for Node.js
beforeAll(() => {
  const __dirname = path.dirname(fileURLToPath(import.meta.url));
  const wasmPath = path.resolve(__dirname, '../../node_modules/@rustledger/wasm/rustledger_wasm_bg.wasm');
  const wasmBuffer = fs.readFileSync(wasmPath);
  initSync({ module: wasmBuffer });
  rustledger.init();
});

// Sample ledger for testing
// Note: Transactions must be in chronological order for balance assertion to work
const SAMPLE_LEDGER = `
2024-01-01 open Assets:Checking USD
2024-01-01 open Expenses:Food USD
2024-01-01 open Income:Salary USD

2024-01-10 * "Employer" "January salary"
  Assets:Checking  5000.00 USD
  Income:Salary   -5000.00 USD

2024-01-15 * "Grocery Store" "Weekly groceries" #food
  Expenses:Food     50.00 USD
  Assets:Checking  -50.00 USD

2024-01-31 balance Assets:Checking 4950.00 USD
`;

// ============================================================================
// WASM Binding Tests
// ============================================================================

describe('rustledger WASM bindings', () => {
  describe('validateSource', () => {
    it('should validate a correct ledger', () => {
      const result = rustledger.validateSource(SAMPLE_LEDGER);
      expect(result.valid).toBe(true);
      expect(result.errors).toHaveLength(0);
    });

    it('should report errors for invalid ledger', () => {
      const invalidLedger = `
2024-01-15 * "Test"
  Expenses:Food  100 USD
  Assets:Checking
`;
      const result = rustledger.validateSource(invalidLedger);
      expect(result.valid).toBe(false);
      expect(result.errors.length).toBeGreaterThan(0);
    });

    // The three shapes from #2084. The reporter's ledger validated clean here
    // while `rledger check` found real errors, and the coverage above could
    // not have caught it: an unopened account is refused during the early
    // phase, whereas a failed assertion and an out-of-balance transaction are
    // only decided once the ledger has been booked. Those are the checks a
    // user reaches for this tool to run.

    it('reports a failed balance assertion', () => {
      const result = rustledger.validateSource(`
2020-01-01 open Assets:Cash USD
2020-01-01 open Equity:O USD

2020-06-01 * "deposit"
  Assets:Cash   100.00 USD
  Equity:O     -100.00 USD

2020-07-01 balance Assets:Cash  -999999.00 USD
`);
      expect(result.valid).toBe(false);
      expect(result.errors.map((e: { code: string }) => e.code)).toContain('E2001');
    });

    it('reports a transaction that does not balance', () => {
      const result = rustledger.validateSource(`
2020-01-01 open Assets:Bank KRW
2020-01-01 open Liabilities:Card KRW
2020-01-01 open Equity:Opening-Balances KRW

2020-01-02 * "opening balances"
  Assets:Bank              1000000 KRW
  Liabilities:Card         -179720 KRW
  Equity:Opening-Balances  -500000 KRW
`);
      expect(result.valid).toBe(false);
      expect(result.errors.map((e: { code: string }) => e.code)).toContain('E3001');
    });

    it('still validates a ledger that also emits a warning', () => {
      // This is the regression itself. Before #1464, `run_validation` bailed
      // on `!load.errors.is_empty()`, so a single plugin WARNING skipped every
      // check that follows — and a large ledger almost always emits one. The
      // assertion below is wrong by a million, and the tool reported success.
      const result = rustledger.validateSource(`
plugin "unrealized" "Equity:Unrealized"
2020-01-01 open Assets:Stock
2020-01-01 open Assets:Cash
2020-01-01 open Equity:Unrealized

2020-01-02 * "buy"
  Assets:Stock  10 AAPL {100.00 USD}
  Assets:Cash  -1000.00 USD

2020-06-01 price AAPL 150.00 USD

2020-07-01 balance Assets:Cash  -999999.00 USD
`);
      const warnings = result.errors.filter(
        (e: { severity: string }) => e.severity === 'warning'
      );
      expect(warnings.length).toBeGreaterThan(0);
      expect(result.valid).toBe(false);
      expect(result.errors.map((e: { code: string }) => e.code)).toContain('E2001');
    });
  });

  describe('query', () => {
    it('should execute BALANCES query', () => {
      const result = rustledger.query(SAMPLE_LEDGER, 'BALANCES');
      expect(result.errors).toHaveLength(0);
      expect(result.columns).toContain('account');
    });

    it('should filter by account', () => {
      const result = rustledger.query(
        SAMPLE_LEDGER,
        'SELECT account, sum(position) WHERE account ~ "Expenses" GROUP BY account'
      );
      expect(result.errors).toHaveLength(0);
      expect(result.rows.length).toBeGreaterThan(0);
    });

    it('should report query errors', () => {
      const result = rustledger.query(SAMPLE_LEDGER, 'INVALID QUERY');
      expect(result.errors.length).toBeGreaterThan(0);
    });
  });

  describe('format', () => {
    it('should format a ledger', () => {
      const result = rustledger.format(SAMPLE_LEDGER);
      expect(result.errors).toHaveLength(0);
      expect(result.formatted).toBeDefined();
      expect(result.formatted!.length).toBeGreaterThan(0);
    });
  });

  describe('parse', () => {
    it('should parse a ledger into directives', () => {
      const result = rustledger.parse(SAMPLE_LEDGER);
      expect(result.errors).toHaveLength(0);
      expect(result.ledger).toBeDefined();
      expect(result.ledger!.directives.length).toBeGreaterThan(0);
    });

    it('should parse different directive types', () => {
      const result = rustledger.parse(SAMPLE_LEDGER);
      const directives = result.ledger!.directives;

      const types = directives.map((d: { type: string }) => d.type);
      expect(types).toContain('open');
      expect(types).toContain('transaction');
      expect(types).toContain('balance');
    });
  });

  describe('listPlugins', () => {
    it('should return available plugins', () => {
      const plugins = rustledger.listPlugins();
      expect(Array.isArray(plugins)).toBe(true);
    });
  });

  describe('bqlCompletions', () => {
    it('should return completions for partial query', () => {
      const result = rustledger.bqlCompletions('SEL', 3);
      expect(result.completions).toBeDefined();
      expect(Array.isArray(result.completions)).toBe(true);
    });
  });
});

describe('ParsedLedger class', () => {
  it('should parse and validate a ledger', () => {
    const ledger = new rustledger.ParsedLedger(SAMPLE_LEDGER);
    expect(ledger.isValid()).toBe(true);
    expect(ledger.getErrors()).toHaveLength(0);
    ledger.free();
  });

  it('should get directives', () => {
    const ledger = new rustledger.ParsedLedger(SAMPLE_LEDGER);
    const directives = ledger.getDirectives();
    expect(directives.length).toBeGreaterThan(0);
    ledger.free();
  });

  it('should run queries', () => {
    const ledger = new rustledger.ParsedLedger(SAMPLE_LEDGER);
    const result = ledger.query('BALANCES');
    expect(result.errors).toHaveLength(0);
    expect(result.columns).toBeDefined();
    ledger.free();
  });

  it('should get document symbols', () => {
    const ledger = new rustledger.ParsedLedger(SAMPLE_LEDGER);
    const symbols = ledger.getDocumentSymbols();
    expect(Array.isArray(symbols)).toBe(true);
    expect(symbols.length).toBeGreaterThan(0);
    ledger.free();
  });

  it('should get completions at position', () => {
    const ledger = new rustledger.ParsedLedger(SAMPLE_LEDGER);
    const result = ledger.getCompletions(4, 2);
    expect(result).toBeDefined();
    expect(result.completions).toBeDefined();
    ledger.free();
  });

  it('should get hover info for account', () => {
    const ledger = new rustledger.ParsedLedger(SAMPLE_LEDGER);
    const result = ledger.getHoverInfo(5, 10);
    expect(result === null || typeof result === 'object').toBe(true);
    ledger.free();
  });

  it('should format the ledger', () => {
    const ledger = new rustledger.ParsedLedger(SAMPLE_LEDGER);
    const result = ledger.format();
    expect(result.formatted).toBeDefined();
    ledger.free();
  });
});

// ============================================================================
// Helper Function Tests
// ============================================================================

describe('Helper Functions', () => {
  describe('validateArgs', () => {
    it('should return null when all required args are present', () => {
      const result = validateArgs({ source: 'test' }, ['source']);
      expect(result).toBeNull();
    });

    it('should return error when required arg is missing', () => {
      const result = validateArgs({}, ['source']);
      expect(result).not.toBeNull();
      expect(result?.isError).toBe(true);
      expect(result?.content[0].text).toContain('source');
    });

    it('should return error listing multiple missing args', () => {
      const result = validateArgs({}, ['source', 'query']);
      expect(result).not.toBeNull();
      expect(result?.content[0].text).toContain('source');
      expect(result?.content[0].text).toContain('query');
    });

    it('should handle undefined args', () => {
      const result = validateArgs(undefined, ['source']);
      expect(result).not.toBeNull();
      expect(result?.isError).toBe(true);
    });
  });

  describe('formatErrors', () => {
    it('should format errors with line numbers', () => {
      const errors = [
        { message: 'Test error', line: 10, column: 5, severity: 'error' as const },
      ];
      const result = formatErrors(errors);
      expect(result).toContain('[error]');
      expect(result).toContain('10:5');
      expect(result).toContain('Test error');
    });

    it('treats only errors as blocking, not warnings', () => {
      // The wasm entry points carry non-fatal notices in the same `errors`
      // array as real failures, so a bare `errors.length > 0` check made a
      // plugin warning fatal. That is how `query` on a ledger using the
      // `unrealized` plugin returned the warning and threw away the rows,
      // where `rledger query` prints them.
      const mixed = [
        { message: 'Unrealized gain', severity: 'warning' as const },
        { message: 'parse error', severity: 'error' as const },
      ];
      expect(fatalErrors(mixed).map((e) => e.message)).toEqual(['parse error']);
      expect(fatalErrors([{ message: 'Unrealized gain', severity: 'warning' as const }])).toEqual([]);
      expect(fatalErrors(undefined)).toEqual([]);
    });

    it('lists warnings on a ledger that is still valid', () => {
      // A warning is not an error — the ledger is valid and `rledger check`
      // exits 0 — but it still has to be SHOWN. Reporting only when `valid` is
      // false meant a ledger the CLI describes as `⚠ 1 warning` came back as a
      // bare "Ledger is valid.", from a tool whose description promises
      // "validation errors and warnings".
      const out = formatValidation({
        valid: true,
        errors: [{ message: 'Unrealized gain on 10 AAPL', severity: 'warning' as const }],
      });
      expect(out).toContain('valid');
      expect(out).toContain('1 warning');
      expect(out).toContain('Unrealized gain on 10 AAPL');
    });

    it('says nothing extra when there is nothing to say', () => {
      expect(formatValidation({ valid: true, errors: [] })).toBe('Ledger is valid.');
    });

    it('counts errors, not warnings, when reporting a failure', () => {
      const out = formatValidation({
        valid: false,
        errors: [
          { message: 'Balance failed', severity: 'error' as const },
          { message: 'Unrealized gain', severity: 'warning' as const },
        ],
      });
      expect(out).toContain('Found 1 error(s)');
      // The warning is still listed — it just does not inflate the count.
      expect(out).toContain('Unrealized gain');
    });

    it('names the file when the error carries one', () => {
      // The multi-file entry points attribute each error to the file it is in.
      // On a ledger split across monthly journals a bare `:561` does not say
      // 561 of WHICH file, which is most of what the location is for.
      const errors = [
        {
          message: 'Balance failed',
          file: 'journals/2021-11.beancount',
          line: 561,
          severity: 'error' as const,
        },
      ];
      expect(formatErrors(errors)).toContain('journals/2021-11.beancount:561');
    });

    it('should handle errors without location', () => {
      const errors = [{ message: 'Generic error', severity: 'warning' as const }];
      const result = formatErrors(errors);
      expect(result).toContain('[warning]');
      expect(result).toContain('Generic error');
    });
  });

  describe('formatQueryResult', () => {
    it('should format query results as table', () => {
      const result = formatQueryResult({
        columns: ['account', 'balance'],
        rows: [['Assets:Checking', '100 USD']],
      });
      expect(result).toContain('account');
      expect(result).toContain('balance');
      expect(result).toContain('Assets:Checking');
    });

    it('should handle empty results', () => {
      const result = formatQueryResult({ columns: [], rows: [] });
      expect(result).toBe('No results.');
    });
  });

  describe('response helpers', () => {
    it('textResponse should create text content', () => {
      const result = textResponse('Hello');
      expect(result.content[0].type).toBe('text');
      expect(result.content[0].text).toBe('Hello');
    });

    it('errorResponse should set isError flag', () => {
      const result = errorResponse('Error message');
      expect(result.isError).toBe(true);
      expect(result.content[0].text).toBe('Error message');
    });

    it('jsonResponse should stringify data', () => {
      const result = jsonResponse({ key: 'value' });
      expect(result.content[0].text).toContain('"key"');
      expect(result.content[0].text).toContain('"value"');
    });
  });
});

// ============================================================================
// Tool Handler Tests
// ============================================================================

describe('Tool Handlers', () => {
  describe('validate', () => {
    it('should validate a correct ledger', () => {
      const result = handleToolCall('validate', { source: SAMPLE_LEDGER });
      expect(result.isError).toBeFalsy();
      expect(result.content[0].text).toContain('valid');
    });

    it('should report validation errors', () => {
      const result = handleToolCall('validate', { source: '2024-01-01 invalid directive' });
      expect(result.content[0].text).toContain('error');
    });

    it('should error on missing source', () => {
      const result = handleToolCall('validate', {});
      expect(result.isError).toBe(true);
      expect(result.content[0].text).toContain('source');
    });
  });

  describe('query', () => {
    it('should execute a query', () => {
      const result = handleToolCall('query', {
        source: SAMPLE_LEDGER,
        query: 'BALANCES',
      });
      expect(result.isError).toBeFalsy();
      expect(result.content[0].text).toContain('account');
    });

    it('should report query errors', () => {
      const result = handleToolCall('query', {
        source: SAMPLE_LEDGER,
        query: 'INVALID QUERY',
      });
      expect(result.isError).toBe(true);
    });

    it('should error on missing arguments', () => {
      const result = handleToolCall('query', { source: SAMPLE_LEDGER });
      expect(result.isError).toBe(true);
      expect(result.content[0].text).toContain('query');
    });
  });

  describe('balances', () => {
    it('should return balances', () => {
      const result = handleToolCall('balances', { source: SAMPLE_LEDGER });
      expect(result.isError).toBeFalsy();
      expect(result.content[0].text).toContain('Assets:Checking');
    });
  });

  describe('format', () => {
    it('should format a ledger', () => {
      const result = handleToolCall('format', { source: SAMPLE_LEDGER });
      expect(result.isError).toBeFalsy();
      expect(result.content[0].text.length).toBeGreaterThan(0);
    });
  });

  describe('parse', () => {
    it('should parse a ledger to JSON', () => {
      const result = handleToolCall('parse', { source: SAMPLE_LEDGER });
      expect(result.isError).toBeFalsy();
      const parsed = JSON.parse(result.content[0].text);
      expect(parsed.directives).toBeDefined();
    });
  });

  describe('list_plugins', () => {
    it('should list available plugins', () => {
      const result = handleToolCall('list_plugins', {});
      expect(result.isError).toBeFalsy();
      const plugins = JSON.parse(result.content[0].text);
      expect(Array.isArray(plugins)).toBe(true);
    });
  });

  describe('editor_completions', () => {
    it('should return completions', () => {
      const result = handleToolCall('editor_completions', {
        source: SAMPLE_LEDGER,
        line: 5,
        character: 2,
      });
      expect(result.isError).toBeFalsy();
    });
  });

  // Regression for #1227: handleImportCategorize used to call
  // `JSON.parse(rustledger.parse(source))` -- threw at runtime because
  // the value was already a JS object. The path also referenced
  // `parsed.directives` instead of `result.ledger.directives`.
  describe('import_categorize', () => {
    it('builds a prompt with the directives traversal working (regression for #1227)', () => {
      const result = handleToolCall('import_categorize', {
        source: SAMPLE_LEDGER,
        narration: 'Coffee',
        date: '2024-01-15',
      });
      expect(result.isError).toBeFalsy();
      // Parse the JSON payload and assert the structural fields the
      // directives traversal populates. SAMPLE_LEDGER opens
      // `Expenses:Food` and `Income:Salary`; both should appear in
      // `known_accounts`. This proves `result.ledger.directives` was
      // walked correctly, not just that the handler didn't throw.
      const payload = JSON.parse(result.content[0].text);
      expect(payload.known_accounts).toContain('Expenses:Food');
      expect(payload.known_accounts).toContain('Income:Salary');
      expect(payload.transaction.narration).toBe('Coffee');
      expect(payload.transaction.date).toBe('2024-01-15');
    });

    it('returns an error response when parsing fails', () => {
      // Pre-fix this would have silently produced a categorization
      // prompt with an empty accounts list; now it surfaces the parser
      // diagnostic, matching `handleParse`'s behavior.
      const result = handleToolCall('import_categorize', {
        source: '@@@ not beancount @@@',
        narration: 'Coffee',
        date: '2024-01-15',
      });
      expect(result.isError).toBeTruthy();
    });

    it('should reject when required args are missing', () => {
      const result = handleToolCall('import_categorize', {});
      expect(result.isError).toBeTruthy();
    });
  });

  // Regression for #1227: handleImportReview had the same broken
  // JSON.parse pattern + wrong directive access path.
  describe('import_review', () => {
    it('reports zero to review when no import-confidence metadata (regression for #1227)', () => {
      const result = handleToolCall('import_review', {
        source: SAMPLE_LEDGER,
      });
      expect(result.isError).toBeFalsy();
      // SAMPLE_LEDGER has no `import-confidence` metadata, so the
      // review summary should report zero across the board. Parsing
      // the JSON payload is what proves the directives walk worked --
      // pre-fix the handler would have thrown before producing any
      // output.
      const payload = JSON.parse(result.content[0].text);
      expect(payload.total).toBe(0);
      expect(payload.high_confidence).toBe(0);
      expect(payload.medium_confidence).toBe(0);
      expect(payload.low_confidence).toBe(0);
    });

    it('returns an error response when parsing fails', () => {
      const result = handleToolCall('import_review', {
        source: '@@@ not beancount @@@',
      });
      expect(result.isError).toBeTruthy();
    });

    it('should reject when source arg is missing', () => {
      const result = handleToolCall('import_review', {});
      expect(result.isError).toBeTruthy();
    });
  });

  describe('editor_hover', () => {
    it('should handle positions without hover info', () => {
      const result = handleToolCall('editor_hover', {
        source: SAMPLE_LEDGER,
        line: 0,
        character: 0,
      });
      expect(result.isError).toBeFalsy();
    });
  });

  describe('editor_definition', () => {
    it('should handle positions without definitions', () => {
      const result = handleToolCall('editor_definition', {
        source: SAMPLE_LEDGER,
        line: 0,
        character: 0,
      });
      expect(result.isError).toBeFalsy();
    });
  });

  describe('editor_document_symbols', () => {
    it('should return document symbols', () => {
      const result = handleToolCall('editor_document_symbols', { source: SAMPLE_LEDGER });
      expect(result.isError).toBeFalsy();
      const symbols = JSON.parse(result.content[0].text);
      expect(Array.isArray(symbols)).toBe(true);
      expect(symbols.length).toBeGreaterThan(0);
    });
  });

  describe('editor_references', () => {
    it('should find account references', () => {
      const result = handleToolCall('editor_references', {
        source: SAMPLE_LEDGER,
        line: 5, // Line with Assets:Checking in a posting
        character: 2,
      });
      expect(result.isError).toBeFalsy();
      // Either finds references or returns "No references found"
      expect(result.content[0].text).toBeDefined();
    });

    it('should find currency references', () => {
      const result = handleToolCall('editor_references', {
        source: SAMPLE_LEDGER,
        line: 5, // Line with USD
        character: 22,
      });
      expect(result.isError).toBeFalsy();
    });

    it('should handle positions without references', () => {
      const result = handleToolCall('editor_references', {
        source: SAMPLE_LEDGER,
        line: 0, // Empty line
        character: 0,
      });
      expect(result.isError).toBeFalsy();
      expect(result.content[0].text).toContain('No references found');
    });
  });

  describe('ledger_stats', () => {
    it('should return ledger statistics', () => {
      const result = handleToolCall('ledger_stats', { source: SAMPLE_LEDGER });
      expect(result.isError).toBeFalsy();
      const stats = JSON.parse(result.content[0].text);
      expect(stats.total_directives).toBeGreaterThan(0);
      expect(stats.transactions).toBe(2);
      expect(stats.open_accounts).toBe(3);
      expect(stats.account_count).toBeGreaterThan(0);
      expect(stats.currencies).toContain('USD');
    });
  });

  describe('list_accounts', () => {
    it('should list all accounts', () => {
      const result = handleToolCall('list_accounts', { source: SAMPLE_LEDGER });
      expect(result.isError).toBeFalsy();
      const accounts = JSON.parse(result.content[0].text);
      expect(accounts['Assets:Checking']).toBeDefined();
      expect(accounts['Assets:Checking'].open_date).toBe('2024-01-01');
    });
  });

  describe('list_commodities', () => {
    it('should list all commodities', () => {
      const result = handleToolCall('list_commodities', { source: SAMPLE_LEDGER });
      expect(result.isError).toBeFalsy();
      const commodities = JSON.parse(result.content[0].text);
      expect(commodities).toContain('USD');
    });
  });

  describe('account_activity', () => {
    it('should return account activity', () => {
      const result = handleToolCall('account_activity', {
        source: SAMPLE_LEDGER,
        account: 'Assets:Checking',
      });
      expect(result.isError).toBeFalsy();
      const activity = JSON.parse(result.content[0].text);
      expect(activity.account).toBe('Assets:Checking');
      expect(activity.transaction_count).toBe(2);
    });
  });

  describe('format_check', () => {
    it('should check if ledger needs formatting', () => {
      const result = handleToolCall('format_check', { source: SAMPLE_LEDGER });
      expect(result.isError).toBeFalsy();
    });
  });

  describe('bql_tables', () => {
    it('should return BQL tables documentation', () => {
      const result = handleToolCall('bql_tables', {});
      expect(result.isError).toBeFalsy();
      expect(result.content[0].text).toContain('entries');
    });
  });

  describe('directive_at_line', () => {
    it('should find directive at line', () => {
      const result = handleToolCall('directive_at_line', {
        source: SAMPLE_LEDGER,
        line: 2,
      });
      expect(result.isError).toBeFalsy();
    });
  });

  describe('find_transactions', () => {
    it('should find transactions by payee', () => {
      const result = handleToolCall('find_transactions', {
        source: SAMPLE_LEDGER,
        payee: 'Grocery',
      });
      expect(result.isError).toBeFalsy();
      const transactions = JSON.parse(result.content[0].text);
      expect(transactions.length).toBe(1);
      expect(transactions[0].payee).toContain('Grocery');
    });

    it('should find transactions by tag', () => {
      const result = handleToolCall('find_transactions', {
        source: SAMPLE_LEDGER,
        tag: 'food',
      });
      expect(result.isError).toBeFalsy();
      const transactions = JSON.parse(result.content[0].text);
      expect(transactions.length).toBe(1);
    });

    it('should filter by date range', () => {
      const result = handleToolCall('find_transactions', {
        source: SAMPLE_LEDGER,
        from_date: '2024-01-12',
      });
      expect(result.isError).toBeFalsy();
      const transactions = JSON.parse(result.content[0].text);
      // Should find the groceries transaction (2024-01-15) but not the salary (2024-01-10)
      expect(transactions.length).toBe(1);
    });

    it('should respect limit', () => {
      const result = handleToolCall('find_transactions', {
        source: SAMPLE_LEDGER,
        limit: 1,
      });
      expect(result.isError).toBeFalsy();
      const transactions = JSON.parse(result.content[0].text);
      expect(transactions.length).toBe(1);
    });
  });

  describe('report', () => {
    it('should generate balance sheet report', () => {
      const result = handleToolCall('report', {
        source: SAMPLE_LEDGER,
        report_type: 'balsheet',
      });
      expect(result.isError).toBeFalsy();
      expect(result.content[0].text).toContain('BALSHEET');
    });

    it('should generate income report', () => {
      const result = handleToolCall('report', {
        source: SAMPLE_LEDGER,
        report_type: 'income',
      });
      expect(result.isError).toBeFalsy();
      expect(result.content[0].text).toContain('INCOME');
    });

    it('should reject unknown report type', () => {
      const result = handleToolCall('report', {
        source: SAMPLE_LEDGER,
        report_type: 'unknown',
      });
      expect(result.isError).toBe(true);
    });
  });

  describe('unknown tool', () => {
    it('should return error for unknown tool', () => {
      const result = handleToolCall('nonexistent_tool', {});
      expect(result.isError).toBe(true);
      expect(result.content[0].text).toContain('Unknown tool');
    });
  });
});

// ============================================================================
// Tool Definition Tests
// ============================================================================

describe('Tool Definitions', () => {
  it('should have 27 tools defined', () => {
    expect(TOOLS.length).toBe(27);
  });

  it('all tools should have required fields', () => {
    for (const tool of TOOLS) {
      expect(tool.name).toBeDefined();
      expect(tool.description).toBeDefined();
      expect(tool.inputSchema).toBeDefined();
      expect(tool.inputSchema.type).toBe('object');
      expect(tool.inputSchema.properties).toBeDefined();
      expect(tool.inputSchema.required).toBeDefined();
    }
  });
});

// ============================================================================
// Resource Tests
// ============================================================================

describe('Resources', () => {
  it('should have 4 resources defined', () => {
    expect(RESOURCES.length).toBe(4);
  });

  it('all resources should have required fields', () => {
    for (const resource of RESOURCES) {
      expect(resource.uri).toBeDefined();
      expect(resource.name).toBeDefined();
      expect(resource.description).toBeDefined();
      expect(resource.mimeType).toBe('text/markdown');
    }
  });

  it('getResourceContents should return content for valid URIs', () => {
    const content = getResourceContents('rustledger://docs/bql');
    expect(content).not.toBeNull();
    expect(content?.mimeType).toBe('text/markdown');
    expect(content?.text.length).toBeGreaterThan(0);
  });

  it('getResourceContents should return null for invalid URIs', () => {
    const content = getResourceContents('rustledger://docs/nonexistent');
    expect(content).toBeNull();
  });
});

// ============================================================================
// Prompt Tests
// ============================================================================

describe('Prompts', () => {
  it('should have 3 prompts defined', () => {
    expect(PROMPTS.length).toBe(3);
  });

  it('all prompts should have required fields', () => {
    for (const prompt of PROMPTS) {
      expect(prompt.name).toBeDefined();
      expect(prompt.description).toBeDefined();
      expect(prompt.arguments).toBeDefined();
    }
  });

  describe('getPrompt', () => {
    it('should return analyze_ledger prompt', () => {
      const result = getPrompt('analyze_ledger', { focus: 'spending' });
      expect(result.messages).toBeDefined();
      expect(result.messages.length).toBe(1);
      expect(result.messages[0].content.text).toContain('spending');
    });

    it('should return write_query prompt', () => {
      const result = getPrompt('write_query', { description: 'find all expenses' });
      expect(result.messages[0].content.text).toContain('find all expenses');
    });

    it('should return categorize_transaction prompt', () => {
      const result = getPrompt('categorize_transaction', { description: 'coffee at starbucks' });
      expect(result.messages[0].content.text).toContain('coffee at starbucks');
    });

    it('should throw for missing required argument', () => {
      expect(() => getPrompt('write_query', {})).toThrow('Missing required argument');
    });

    it('should throw for unknown prompt', () => {
      expect(() => getPrompt('unknown_prompt', {})).toThrow('Unknown prompt');
    });
  });
});

// ============================================================================
// Include Resolution Tests
// ============================================================================
describe('collectLedgerFiles', () => {
  // Discovery only. Include SEMANTICS — resolution order, glob expansion, a
  // file reached twice, cycles, and which file and line an error belongs to —
  // are asserted against the loader through `validateMultiFile`, because that
  // is where they now live. This function's job is to put candidate files in
  // the map; over-collecting is harmless and under-collecting is reported by
  // the loader against the file that asked.
  let tempDir: string;

  beforeAll(() => {
    tempDir = fs.mkdtempSync(path.join(os.tmpdir(), 'mcp-collect-'));
  });

  const write = (rel: string, content: string): string => {
    const abs = path.join(tempDir, rel);
    fs.mkdirSync(path.dirname(abs), { recursive: true });
    fs.writeFileSync(abs, content);
    return abs;
  };

  it('collects a single file with no includes', () => {
    const main = write('solo/main.beancount', '2024-01-01 open Assets:Cash USD\n');
    const { files, entry } = collectLedgerFiles(main);
    expect(entry).toBe('main.beancount');
    expect(Object.keys(files)).toEqual(['main.beancount']);
  });

  it('collects an include, keyed relative to the entry point', () => {
    write('one/accounts.beancount', '2024-01-01 open Assets:Cash USD\n');
    const main = write('one/main.beancount', 'include "accounts.beancount"\n');
    const { files } = collectLedgerFiles(main);
    expect(Object.keys(files).sort()).toEqual(['accounts.beancount', 'main.beancount']);
  });

  it('collects nested includes and uses forward slashes in keys', () => {
    write('nest/sub/deep.beancount', '2024-01-01 open Assets:Deep USD\n');
    write('nest/sub/level1.beancount', 'include "deep.beancount"\n');
    const main = write('nest/main.beancount', 'include "sub/level1.beancount"\n');
    const { files } = collectLedgerFiles(main);
    expect(Object.keys(files).sort()).toEqual([
      'main.beancount',
      'sub/deep.beancount',
      'sub/level1.beancount',
    ]);
  });

  it('collects a file reached twice exactly once, and the loader decides the rest', () => {
    // A diamond. The map is unique by construction, so the doubling that a
    // concatenating loader had to guard against cannot arise here at all.
    write('dia/sub/shared.beancount',
      '2020-03-01 * "shared txn"\n  Expenses:Food   100.00 USD\n  Assets:Cash    -100.00 USD\n');
    write('dia/sub/mid.beancount', 'include "shared.beancount"\n');
    const main = write('dia/main.beancount',
      '2020-01-01 open Assets:Cash USD\n2020-01-01 open Expenses:Food USD\n' +
      'include "sub/shared.beancount"\ninclude "sub/mid.beancount"\n' +
      '2020-06-01 balance Assets:Cash -100.00 USD\n');

    const { files, entry } = collectLedgerFiles(main);
    expect(Object.keys(files).sort()).toEqual([
      'main.beancount', 'sub/mid.beancount', 'sub/shared.beancount',
    ]);
    // The map is unique by construction, so the shared file contributes once
    // and the balance holds at 100.00 rather than doubling to 200.00. That is
    // this test's subject and it is unchanged.
    //
    // The loader now REPORTS the diamond, matching Python's
    // `Duplicate filename parsed`, so the result is no longer `valid`. The
    // sibling test above asserts that report directly; here it only means the
    // verdict flipped, not that the collection doubled. Naming the specific
    // message keeps this test honest about WHY it is invalid -- a doubled
    // balance would surface as a balance-assertion failure, which this would
    // not accept.
    const result = rustledger.validateMultiFile(files, entry);
    expect(result.valid).toBe(false);
    expect(
      result.errors.some((e) => e.message.includes('Duplicate filename parsed')),
    ).toBe(true);
  });

  it('collects every file a glob matches', () => {
    // `include "j/*.beancount"` is how a ledger split into monthly files is
    // written. The loader expands the pattern itself over the virtual
    // filesystem; discovery just has to have put the files there.
    for (const m of ['01', '02', '03']) {
      write(`glob/j/2020-${m}.beancount`,
        `2020-${m}-05 * "t${m}"\n  Expenses:Food   1${m}.00 USD\n  Assets:Cash    -1${m}.00 USD\n`);
    }
    const main = write('glob/main.beancount',
      '2020-01-01 open Assets:Cash USD\n2020-01-01 open Expenses:Food USD\ninclude "j/*.beancount"\n');

    const { files, entry } = collectLedgerFiles(main);
    expect(Object.keys(files).sort()).toEqual([
      'j/2020-01.beancount', 'j/2020-02.beancount', 'j/2020-03.beancount', 'main.beancount',
    ]);
    const q = rustledger.queryMultiFile(
      files, entry, "SELECT sum(number(position)) AS n WHERE account='Expenses:Food'");
    expect(q.rows[0][0]).toContain('306');
  });

  it('does not collect a directory a glob happens to match', () => {
    // beancount 3.2.3 dies with an unhandled IsADirectoryError here and
    // `rledger check` reports `Is a directory`. Only files can be included.
    fs.mkdirSync(path.join(tempDir, 'gdir/d/subdir'), { recursive: true });
    write('gdir/d/x.beancount',
      '2020-03-01 * "t"\n  Expenses:Food   10.00 USD\n  Assets:Cash    -10.00 USD\n');
    const main = write('gdir/main.beancount',
      '2020-01-01 open Assets:Cash USD\n2020-01-01 open Expenses:Food USD\ninclude "d/*"\n');

    const { files, entry } = collectLedgerFiles(main);
    expect(Object.keys(files).sort()).toEqual(['d/x.beancount', 'main.beancount']);
    expect(rustledger.validateMultiFile(files, entry).valid).toBe(true);
  });

  it('terminates on a cycle and lets the loader report it', () => {
    // Discovery must not recurse forever; the VERDICT is the loader's, and its
    // wording matches `rledger check` because it is the same code.
    write('cyc/b.beancount', 'include "a.beancount"\n');
    const main = write('cyc/a.beancount', 'include "b.beancount"\n');

    const { files, entry } = collectLedgerFiles(main);
    expect(Object.keys(files).sort()).toEqual(['a.beancount', 'b.beancount']);
    const result = rustledger.validateMultiFile(files, entry);
    expect(result.valid).toBe(false);
    expect(result.errors[0].message).toContain('Duplicate filename parsed');
    expect(result.errors[0].message).toContain('include cycle');
  });

  it('terminates when a glob matches its own file', () => {
    const main = write('gself/self.beancount', 'include "*.beancount"\n');
    const { files, entry } = collectLedgerFiles(main);
    expect(Object.keys(files)).toEqual(['self.beancount']);
    expect(rustledger.validateMultiFile(files, entry).errors[0].message).toContain(
      'Duplicate filename parsed'
    );
  });

  it('leaves a glob that matches nothing to the loader', () => {
    const main = write('gnone/main.beancount', 'include "nothing/*.beancount"\n');
    const { files, entry } = collectLedgerFiles(main);
    expect(Object.keys(files)).toEqual(['main.beancount']);
    const result = rustledger.validateMultiFile(files, entry);
    expect(result.errors[0].message).toContain('does not match any files');
  });

  it('leaves a missing include to the loader', () => {
    // Discovery cannot read it, so it stays out of the map and the loader
    // reports it against the file that asked — better placed than anything
    // this function could say.
    const main = write('gone/main.beancount', 'include "gone.beancount"\n');
    const { files, entry } = collectLedgerFiles(main);
    expect(Object.keys(files)).toEqual(['main.beancount']);
    const result = rustledger.validateMultiFile(files, entry);
    expect(result.errors[0].message).toContain('gone.beancount');
  });

  it('reports a file reached twice, once the wasm carries the loader fix', () => {
    const dir = fs.mkdtempSync(path.join(os.tmpdir(), 'mcp-dupwasm-'));
    fs.mkdirSync(path.join(dir, 'sub'), { recursive: true });
    fs.writeFileSync(path.join(dir, 'sub/shared.beancount'), '2020-01-01 open Assets:Cash USD\n');
    fs.writeFileSync(path.join(dir, 'sub/mid.beancount'), 'include "shared.beancount"\n');
    const main = path.join(dir, 'dup.beancount');
    fs.writeFileSync(main, 'include "sub/shared.beancount"\ninclude "sub/mid.beancount"\n');

    const { files, entry } = collectLedgerFiles(main);
    const result = rustledger.validateMultiFile(files, entry);
    expect(result.errors.some((e: { message: string }) =>
      e.message.includes('Duplicate filename parsed'))).toBe(true);
  });

  it('resolves includes relative to a symlinked entry point\'s real directory', () => {
    // A relative include resolves against the directory the file really lives
    // in. Reading through a symlinked entry and then resolving its includes
    // beside the LINK looked for files that are not there, so the whole ledger
    // failed with `file not found` on a tree `rledger check` reads fine.
    const dir = fs.mkdtempSync(path.join(os.tmpdir(), 'mcp-linkentry-'));
    fs.mkdirSync(path.join(dir, 'real'), { recursive: true });
    fs.writeFileSync(
      path.join(dir, 'real/x.beancount'),
      '2020-03-01 * "t"\n  Expenses:Food   10.00 USD\n  Assets:Cash    -10.00 USD\n'
    );
    fs.writeFileSync(
      path.join(dir, 'real/main.beancount'),
      '2020-01-01 open Assets:Cash USD\n2020-01-01 open Expenses:Food USD\ninclude "x.beancount"\n'
    );
    const link = path.join(dir, 'entry.beancount');
    fs.symlinkSync(path.join(dir, 'real/main.beancount'), link);

    const { files, entry } = collectLedgerFiles(link);
    expect(Object.keys(files).sort()).toEqual(['main.beancount', 'x.beancount']);
    expect(entry).toBe('main.beancount');
    const result = rustledger.queryMultiFile(
      files,
      entry,
      "SELECT sum(number(position)) AS n WHERE account='Expenses:Food'"
    );
    expect(result.rows[0][0]).toContain('10.00');
  });

  it('does not count a symlinked file twice', () => {
    // `path.resolve` normalizes `.` and `..` but not symlinks, so a file
    // reached both directly and through a link used to land under two keys —
    // and a VirtualFileSystem has no symlinks to collapse them again, so the
    // loader read the same directives twice and silently doubled every amount
    // in that file: 20.00 where `rledger check` says 10.00.
    //
    // The alias still has to resolve, since an include names it, so it stands
    // in a one-line include of the canonical copy.
    const dir = fs.mkdtempSync(path.join(os.tmpdir(), 'mcp-symlink-'));
    fs.mkdirSync(path.join(dir, 'j'), { recursive: true });
    fs.writeFileSync(
      path.join(dir, 'j/x.beancount'),
      '2020-03-01 * "t"\n  Expenses:Food   10.00 USD\n  Assets:Cash    -10.00 USD\n'
    );
    fs.symlinkSync(path.join(dir, 'j/x.beancount'), path.join(dir, 'link.beancount'));
    const main = path.join(dir, 'sym.beancount');
    fs.writeFileSync(
      main,
      '2020-01-01 open Assets:Cash USD\n2020-01-01 open Expenses:Food USD\n' +
        'include "j/x.beancount"\ninclude "link.beancount"\n'
    );

    const { files, entry } = collectLedgerFiles(main);
    const result = rustledger.queryMultiFile(
      files,
      entry,
      "SELECT sum(number(position)) AS n WHERE account='Expenses:Food'"
    );
    expect(result.rows[0][0]).toContain('10.00');
  });

  it('attributes an error to the file and line it is on', () => {
    // The reason this architecture exists. Concatenating the ledger into one
    // string reported this same error as `file: null, line: 9` — a position in
    // the concatenation that appears in none of the user's files.
    write('attr/j/2020-06.beancount',
      '2020-06-01 * "deposit"\n  Assets:Cash   100.00 USD\n  Equity:O     -100.00 USD\n');
    write('attr/j/2020-07.beancount', '\n2020-07-01 balance Assets:Cash  -999999.00 USD\n');
    const main = write('attr/main.beancount',
      'option "operating_currency" "USD"\n2020-01-01 open Assets:Cash USD\n' +
      '2020-01-01 open Equity:O USD\ninclude "j/2020-06.beancount"\ninclude "j/2020-07.beancount"\n');

    const { files, entry } = collectLedgerFiles(main);
    const result = rustledger.validateMultiFile(files, entry);
    expect(result.valid).toBe(false);
    expect(result.errors[0].file).toBe('j/2020-07.beancount');
    expect(result.errors[0].line).toBe(2);
  });
});

describe('File Handlers with Include Resolution', () => {
  let tempDir: string;

  beforeAll(() => {
    tempDir = fs.mkdtempSync(path.join(os.tmpdir(), 'mcp-file-test-'));
  });

  afterAll(() => {
    fs.rmSync(tempDir, { recursive: true, force: true });
  });

  describe('query_file', () => {
    it('should query a file with includes resolved', () => {
      const accountsPath = path.join(tempDir, 'accounts.beancount');
      const transactionsPath = path.join(tempDir, 'transactions.beancount');
      const mainPath = path.join(tempDir, 'query-main.beancount');

      fs.writeFileSync(accountsPath, `2024-01-01 open Assets:Bank USD
2024-01-01 open Expenses:Food USD
`);
      fs.writeFileSync(transactionsPath, `2024-01-15 * "Grocery Store" "Food"
  Expenses:Food  100 USD
  Assets:Bank  -100 USD
`);
      fs.writeFileSync(mainPath, `include "accounts.beancount"
include "transactions.beancount"
`);

      const result = handleToolCall('query_file', {
        file_path: mainPath,
        query: 'SELECT count(*)',
      });

      expect(result.isError).toBeFalsy();
      // Should find 2 postings from the transaction in the included file
      expect(result.content[0].text).toContain('2');
    });
  });

  describe('validate_file', () => {
    it('should validate a file with includes resolved', () => {
      const accountsPath = path.join(tempDir, 'val-accounts.beancount');
      const mainPath = path.join(tempDir, 'val-main.beancount');

      fs.writeFileSync(accountsPath, `2024-01-01 open Assets:Checking USD
2024-01-01 open Expenses:Food USD
`);
      fs.writeFileSync(mainPath, `include "val-accounts.beancount"

2024-01-15 * "Test"
  Expenses:Food  50 USD
  Assets:Checking  -50 USD
`);

      const result = handleToolCall('validate_file', {
        file_path: mainPath,
      });

      expect(result.isError).toBeFalsy();
      expect(result.content[0].text).toContain('valid');
    });

    it('should report errors from included files', () => {
      const badAccountsPath = path.join(tempDir, 'bad-accounts.beancount');
      const badMainPath = path.join(tempDir, 'bad-main.beancount');

      // Note: Transaction uses an account that's never opened
      fs.writeFileSync(badAccountsPath, `2024-01-01 open Assets:Bank USD`);
      fs.writeFileSync(badMainPath, `include "bad-accounts.beancount"

2024-01-15 * "Test"
  Expenses:Unopened  50 USD
  Assets:Bank  -50 USD
`);

      const result = handleToolCall('validate_file', {
        file_path: badMainPath,
      });

      // Should report the missing account error
      expect(result.content[0].text).toContain('error');
    });
  });
});

// ============================================================================
// Editor tools: file_path + include resolution (#1328)
// ============================================================================

describe('withIncludedContext', () => {
  let tempDir: string;

  beforeAll(() => {
    tempDir = fs.mkdtempSync(path.join(os.tmpdir(), 'mcp-ctx-'));
  });
  afterAll(() => {
    fs.rmSync(tempDir, { recursive: true, force: true });
  });

  it('returns the source unchanged when it includes nothing', () => {
    const src = '2024-01-01 open Assets:Bank USD\n';
    expect(withIncludedContext(src, tempDir)).toBe(src);
  });

  it('appends included contents AFTER the edited source (line numbers preserved)', () => {
    fs.writeFileSync(path.join(tempDir, 'journal.beancount'), '2024-01-01 open Assets:Cash USD');
    const edited = 'include "journal.beancount"\n2024-01-01 open Assets:Bank USD\n';
    const full = withIncludedContext(edited, tempDir);
    // The edited document is a verbatim prefix — so a (line, character)
    // cursor into it still resolves correctly.
    expect(full.startsWith(edited)).toBe(true);
    // The included account is present for aggregate lookups.
    expect(full).toContain('Assets:Cash');
  });

  it('de-duplicates a diamond include graph', () => {
    const d = fs.mkdtempSync(path.join(os.tmpdir(), 'mcp-diamond-'));
    fs.writeFileSync(path.join(d, 'shared.beancount'), '2024-01-01 open Assets:Shared USD');
    fs.writeFileSync(path.join(d, 'b.beancount'), 'include "shared.beancount"');
    fs.writeFileSync(path.join(d, 'c.beancount'), 'include "shared.beancount"');
    const edited = 'include "b.beancount"\ninclude "c.beancount"\n';
    const full = withIncludedContext(edited, d);
    const occurrences = full.split('Assets:Shared').length - 1;
    expect(occurrences).toBe(1);
    fs.rmSync(d, { recursive: true, force: true });
  });

  it('throws a contextual error for a missing include', () => {
    const edited = 'include "does-not-exist.beancount"\n';
    expect(() => withIncludedContext(edited, tempDir)).toThrow(/Failed to include "does-not-exist\.beancount"/);
  });

  it('resolves an include that has a trailing comment', () => {
    fs.writeFileSync(path.join(tempDir, 'commented.beancount'), '2024-01-01 open Assets:Commented USD');
    const edited = 'include "commented.beancount" ; monthly journal\n';
    const full = withIncludedContext(edited, tempDir);
    expect(full).toContain('Assets:Commented');
  });

  it('resolves an include on a BOM-prefixed first line', () => {
    fs.writeFileSync(path.join(tempDir, 'bom-target.beancount'), '2024-01-01 open Assets:Bom USD');
    const edited = '﻿include "bom-target.beancount"\n';
    const full = withIncludedContext(edited, tempDir);
    expect(full).toContain('Assets:Bom');
  });

  it('preserves the edited document verbatim when it lacks a trailing newline', () => {
    fs.writeFileSync(path.join(tempDir, 'nl-target.beancount'), '2024-01-01 open Assets:NlInc USD');
    // No trailing newline on the edited source.
    const edited = 'include "nl-target.beancount"\n2024-01-01 open Assets:NoNl USD';
    const full = withIncludedContext(edited, tempDir);
    // The join inserts a separator, so the edited doc's last line stays intact
    // (cursor coordinates into it remain valid) and both accounts are present.
    expect(full.startsWith(edited)).toBe(true);
    expect(full).toContain('Assets:NoNl');
    expect(full).toContain('Assets:NlInc');
  });

  it('resolves a CRLF include line', () => {
    fs.writeFileSync(path.join(tempDir, 'crlf-target.beancount'), '2024-01-01 open Assets:Crlf USD');
    const edited = 'include "crlf-target.beancount"\r\n2024-01-01 open Assets:Main USD\r\n';
    const full = withIncludedContext(edited, tempDir);
    expect(full).toContain('Assets:Crlf');
  });

  it('is cycle-safe: a circular include graph terminates and appends each file once', () => {
    const d = fs.mkdtempSync(path.join(os.tmpdir(), 'mcp-cycle-'));
    fs.writeFileSync(path.join(d, 'a.beancount'), 'include "b.beancount"\n2024-01-01 open Assets:A USD');
    fs.writeFileSync(path.join(d, 'b.beancount'), 'include "a.beancount"\n2024-01-01 open Assets:B USD');
    // The global `visited` set is added to BEFORE recursing, so A -> B -> A
    // terminates (no infinite loop) and each file is appended exactly once.
    const full = withIncludedContext('include "a.beancount"\n', d);
    expect(full.split('Assets:A').length - 1).toBe(1);
    expect(full.split('Assets:B').length - 1).toBe(1);
    fs.rmSync(d, { recursive: true, force: true });
  });
});

describe('editor tools with file_path', () => {
  let tempDir: string;
  let mainPath: string;

  beforeAll(() => {
    tempDir = fs.mkdtempSync(path.join(os.tmpdir(), 'mcp-editor-'));
    // journal.beancount defines Assets:Checking and uses it in one posting.
    fs.writeFileSync(
      path.join(tempDir, 'journal.beancount'),
      `2024-01-01 open Assets:Checking USD
2024-01-01 open Income:Salary USD
2024-01-10 * "Salary"
  Assets:Checking  100.00 USD
  Income:Salary   -100.00 USD
`
    );
    // main.beancount includes the journal and uses Assets:Checking once more.
    mainPath = path.join(tempDir, 'main.beancount');
    fs.writeFileSync(
      mainPath,
      `include "journal.beancount"
2024-01-01 open Expenses:Food USD
2024-02-01 * "Coffee"
  Assets:Checking  -5.00 USD
  Expenses:Food     5.00 USD
`
    );
  });
  afterAll(() => {
    fs.rmSync(tempDir, { recursive: true, force: true });
  });

  // The hover cursor sits on `Assets:Checking` in main.beancount
  // (line 3 = the Coffee posting, column 5 is inside the account name).
  const HOVER_LINE = 3;
  const HOVER_CHAR = 5;

  function hoverContents(result: { content: Array<{ text: string }> }): string {
    return result.content[0].text;
  }

  it('editor_hover resolves includes: open is found and the posting count is whole-ledger', () => {
    const result = handleToolCall('editor_hover', {
      file_path: mainPath,
      line: HOVER_LINE,
      character: HOVER_CHAR,
    });
    const text = hoverContents(result);
    // The Open lives in the included journal — found only with include resolution.
    expect(text).toContain('Opened:');
    // Used in 2 postings: the Coffee posting (main) + the Salary posting (journal).
    expect(text).toContain('Used in:** 2 postings');
  });

  it('editor_hover without file_path sees only the edited file (no open, fewer postings)', () => {
    const source = fs.readFileSync(mainPath, 'utf-8');
    const result = handleToolCall('editor_hover', {
      source,
      line: HOVER_LINE,
      character: HOVER_CHAR,
    });
    const text = hoverContents(result);
    // Open is in the (unresolved) include, so it's reported as missing...
    expect(text).toContain('No `open` directive found');
    // ...and only the single in-file posting is counted.
    expect(text).toContain('Used in:** 1 postings');
  });

  it('source overrides file_path contents while file_path still anchors includes', () => {
    // Unsaved buffer adds a SECOND in-file posting of Assets:Checking.
    const buffer = `include "journal.beancount"
2024-01-01 open Expenses:Food USD
2024-02-01 * "Coffee"
  Assets:Checking  -5.00 USD
  Expenses:Food     5.00 USD
2024-02-02 * "Tea"
  Assets:Checking  -3.00 USD
  Expenses:Food     3.00 USD
`;
    const result = handleToolCall('editor_hover', {
      source: buffer,
      file_path: mainPath,
      line: HOVER_LINE,
      character: HOVER_CHAR,
    });
    const text = hoverContents(result);
    // 2 in-buffer postings + 1 from the resolved journal = 3.
    expect(text).toContain('Used in:** 3 postings');
  });

  it('editor_hover errors when neither source nor file_path is given', () => {
    const result = handleToolCall('editor_hover', { line: 0, character: 0 });
    expect(result.isError).toBe(true);
    expect(result.content[0].text).toMatch(/Provide either 'source'.*'file_path'/);
  });

  it('editor_hover errors for a nonexistent file_path', () => {
    const result = handleToolCall('editor_hover', {
      file_path: path.join(tempDir, 'nope.beancount'),
      line: 0,
      character: 0,
    });
    expect(result.isError).toBe(true);
    expect(result.content[0].text).toContain('Error reading file');
  });

  it('editor_completions offers accounts defined in included files', () => {
    // Cursor at the start of an empty posting line in a fresh buffer that
    // includes the journal; completions should surface Assets:Checking.
    const buffer = `include "journal.beancount"
2024-03-01 * "x"
  Assets`;
    const result = handleToolCall('editor_completions', {
      source: buffer,
      file_path: mainPath,
      line: 2,
      character: 8,
    });
    expect(result.content[0].text).toContain('Assets:Checking');
  });

  it('editor_document_symbols stays document-local (does not inline includes)', () => {
    const result = handleToolCall('editor_document_symbols', { file_path: mainPath });
    const symbols = JSON.parse(result.content[0].text);
    // main.beancount has its own directives; the journal's Income:Salary open
    // must NOT appear (includes are not inlined for the outline).
    const text = JSON.stringify(symbols);
    expect(text).toContain('Expenses:Food');
    expect(text).not.toContain('Income:Salary');
  });

  it('editor_definition reads file_path from disk (document-local)', () => {
    // Define + use an account in a single self-contained file.
    const selfContained = path.join(tempDir, 'solo.beancount');
    fs.writeFileSync(
      selfContained,
      `2024-01-01 open Assets:Solo USD
2024-01-02 * "x"
  Assets:Solo  1.00 USD
  Expenses:Misc
`
    );
    const result = handleToolCall('editor_definition', {
      file_path: selfContained,
      line: 2,
      character: 5,
    });
    // Either a definition object or the "no definition" text — but never an
    // input error, proving the file was loaded.
    expect(result.isError).toBeFalsy();
  });
});
