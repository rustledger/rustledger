import { describe, it, expect, beforeAll, afterAll } from 'vitest';
import * as fs from 'fs';
import * as path from 'path';
import * as os from 'os';
import { fileURLToPath } from 'url';
import { initSync } from '@rustledger/wasm';
import * as rustledger from '@rustledger/wasm';
import { handleToolCall } from '../handlers.js';
import { validateArgs, formatErrors, formatQueryResult, textResponse, errorResponse, jsonResponse, loadWithIncludes } from '../helpers.js';
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
      expect(result).toContain(':10:5');
      expect(result).toContain('Test error');
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

describe('loadWithIncludes', () => {
  let tempDir: string;

  beforeAll(() => {
    // Create a temporary directory for test files
    tempDir = fs.mkdtempSync(path.join(os.tmpdir(), 'mcp-test-'));
  });

  afterAll(() => {
    // Clean up temp files
    fs.rmSync(tempDir, { recursive: true, force: true });
  });

  it('should load a single file without includes', () => {
    const filePath = path.join(tempDir, 'single.beancount');
    fs.writeFileSync(filePath, '2024-01-01 open Assets:Bank USD');

    const result = loadWithIncludes(filePath);
    expect(result).toBe('2024-01-01 open Assets:Bank USD');
  });

  it('should resolve a single include', () => {
    const mainPath = path.join(tempDir, 'main.beancount');
    const includedPath = path.join(tempDir, 'accounts.beancount');

    fs.writeFileSync(includedPath, '2024-01-01 open Assets:Cash USD');
    fs.writeFileSync(mainPath, `include "accounts.beancount"

2024-01-15 * "Test"
  Expenses:Food  10 USD
  Assets:Cash  -10 USD
`);

    const result = loadWithIncludes(mainPath);
    expect(result).toContain('2024-01-01 open Assets:Cash USD');
    expect(result).toContain('2024-01-15 * "Test"');
  });

  it('should resolve nested includes', () => {
    const mainPath = path.join(tempDir, 'nested-main.beancount');
    const level1Path = path.join(tempDir, 'level1.beancount');
    const level2Path = path.join(tempDir, 'level2.beancount');

    fs.writeFileSync(level2Path, '2024-01-01 open Assets:Nested USD');
    fs.writeFileSync(level1Path, `include "level2.beancount"
2024-01-01 open Expenses:Food USD
`);
    fs.writeFileSync(mainPath, `include "level1.beancount"
2024-01-15 * "Transaction"
  Expenses:Food  5 USD
  Assets:Nested  -5 USD
`);

    const result = loadWithIncludes(mainPath);
    expect(result).toContain('Assets:Nested');
    expect(result).toContain('Expenses:Food');
    expect(result).toContain('Transaction');
  });

  it('should resolve includes with relative paths', () => {
    const subDir = path.join(tempDir, 'subdir');
    fs.mkdirSync(subDir, { recursive: true });

    const mainPath = path.join(tempDir, 'rel-main.beancount');
    const includedPath = path.join(subDir, 'sub-file.beancount');

    fs.writeFileSync(includedPath, '2024-01-01 open Assets:SubDir USD');
    fs.writeFileSync(mainPath, 'include "subdir/sub-file.beancount"');

    const result = loadWithIncludes(mainPath);
    expect(result).toContain('Assets:SubDir');
  });

  it('should detect circular includes', () => {
    const file1Path = path.join(tempDir, 'circular1.beancount');
    const file2Path = path.join(tempDir, 'circular2.beancount');

    fs.writeFileSync(file1Path, 'include "circular2.beancount"');
    fs.writeFileSync(file2Path, 'include "circular1.beancount"');

    // Verify error message contains the file path for debugging
    expect(() => loadWithIncludes(file1Path)).toThrow(/Circular include.*circular1\.beancount/);
  });

  it('should allow diamond includes (same file from different branches)', () => {
    // Test case: A includes B and C, both B and C include D
    // This should NOT be detected as circular - D is included twice but not in a cycle
    const mainPath = path.join(tempDir, 'diamond-main.beancount');
    const branchBPath = path.join(tempDir, 'diamond-b.beancount');
    const branchCPath = path.join(tempDir, 'diamond-c.beancount');
    const sharedPath = path.join(tempDir, 'diamond-shared.beancount');

    fs.writeFileSync(sharedPath, '2024-01-01 open Assets:Shared USD');
    fs.writeFileSync(branchBPath, 'include "diamond-shared.beancount"\n2024-01-01 open Assets:B USD');
    fs.writeFileSync(branchCPath, 'include "diamond-shared.beancount"\n2024-01-01 open Assets:C USD');
    fs.writeFileSync(mainPath, 'include "diamond-b.beancount"\ninclude "diamond-c.beancount"');

    // Should succeed - the shared file is included twice but not circularly
    const result = loadWithIncludes(mainPath);
    expect(result).toContain('Assets:Shared');
    expect(result).toContain('Assets:B');
    expect(result).toContain('Assets:C');
  });

  it('should throw error for missing included file', () => {
    const mainPath = path.join(tempDir, 'missing-include.beancount');
    fs.writeFileSync(mainPath, 'include "nonexistent.beancount"');

    expect(() => loadWithIncludes(mainPath)).toThrow('Failed to include');
  });
});

// ============================================================================
// File Handler Tests with Includes
// ============================================================================

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
