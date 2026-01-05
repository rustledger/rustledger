#!/usr/bin/env node

import { Server } from "@modelcontextprotocol/sdk/server/index.js";
import { StdioServerTransport } from "@modelcontextprotocol/sdk/server/stdio.js";
import {
  CallToolRequestSchema,
  ListToolsRequestSchema,
  ListResourcesRequestSchema,
  ReadResourceRequestSchema,
} from "@modelcontextprotocol/sdk/types.js";

// Import rustledger WASM bindings
import * as rustledger from "@rustledger/wasm";

// Initialize WASM module
rustledger.init();

const server = new Server(
  {
    name: "rustledger",
    version: rustledger.version(),
  },
  {
    capabilities: {
      tools: {},
      resources: {},
    },
  }
);

// Tool definitions
const TOOLS = [
  {
    name: "validate",
    description:
      "Validate a Beancount ledger. Returns validation errors and warnings if any issues are found.",
    inputSchema: {
      type: "object" as const,
      properties: {
        source: {
          type: "string",
          description: "The Beancount ledger source text to validate",
        },
      },
      required: ["source"],
    },
  },
  {
    name: "query",
    description:
      "Run a BQL (Beancount Query Language) query on a ledger. Use this for account balances, filtering transactions, aggregations, etc.",
    inputSchema: {
      type: "object" as const,
      properties: {
        source: {
          type: "string",
          description: "The Beancount ledger source text",
        },
        query: {
          type: "string",
          description:
            'The BQL query to execute (e.g., "SELECT account, sum(position) GROUP BY account")',
        },
      },
      required: ["source", "query"],
    },
  },
  {
    name: "balances",
    description:
      "Get account balances from a ledger. This is a shorthand for running a BALANCES query.",
    inputSchema: {
      type: "object" as const,
      properties: {
        source: {
          type: "string",
          description: "The Beancount ledger source text",
        },
      },
      required: ["source"],
    },
  },
  {
    name: "format",
    description:
      "Format a Beancount ledger with consistent alignment and spacing.",
    inputSchema: {
      type: "object" as const,
      properties: {
        source: {
          type: "string",
          description: "The Beancount ledger source text to format",
        },
      },
      required: ["source"],
    },
  },
  {
    name: "parse",
    description:
      "Parse a Beancount ledger and return the directives as structured data.",
    inputSchema: {
      type: "object" as const,
      properties: {
        source: {
          type: "string",
          description: "The Beancount ledger source text to parse",
        },
      },
      required: ["source"],
    },
  },
  {
    name: "completions",
    description:
      "Get BQL query completions at a cursor position. Useful for building query editors.",
    inputSchema: {
      type: "object" as const,
      properties: {
        partial_query: {
          type: "string",
          description: "The partial BQL query text",
        },
        cursor_pos: {
          type: "number",
          description: "The cursor position (character offset) in the query",
        },
      },
      required: ["partial_query", "cursor_pos"],
    },
  },
  {
    name: "list_plugins",
    description: "List available native plugins that can process ledgers.",
    inputSchema: {
      type: "object" as const,
      properties: {},
      required: [],
    },
  },
  {
    name: "run_plugin",
    description: "Run a native plugin on a ledger.",
    inputSchema: {
      type: "object" as const,
      properties: {
        source: {
          type: "string",
          description: "The Beancount ledger source text",
        },
        plugin_name: {
          type: "string",
          description:
            "The name of the plugin to run (use list_plugins to see available plugins)",
        },
      },
      required: ["source", "plugin_name"],
    },
  },
];

// List available tools
server.setRequestHandler(ListToolsRequestSchema, async () => {
  return { tools: TOOLS };
});

// Handle tool calls
server.setRequestHandler(CallToolRequestSchema, async (request) => {
  const { name, arguments: args } = request.params;

  try {
    switch (name) {
      case "validate": {
        const source = args?.source as string;
        if (!source) {
          return {
            isError: true,
            content: [{ type: "text", text: "Missing required argument: source" }],
          };
        }
        const result = rustledger.validateSource(source);
        return {
          content: [
            {
              type: "text",
              text: result.valid
                ? "Ledger is valid."
                : `Found ${result.errors.length} error(s):\n${formatErrors(result.errors)}`,
            },
          ],
        };
      }

      case "query": {
        const source = args?.source as string;
        const query = args?.query as string;
        if (!source || !query) {
          return {
            isError: true,
            content: [
              { type: "text", text: "Missing required arguments: source and query" },
            ],
          };
        }
        const result = rustledger.query(source, query);
        if (result.errors?.length > 0) {
          return {
            isError: true,
            content: [{ type: "text", text: formatErrors(result.errors) }],
          };
        }
        return {
          content: [{ type: "text", text: formatQueryResult(result) }],
        };
      }

      case "balances": {
        const source = args?.source as string;
        if (!source) {
          return {
            isError: true,
            content: [{ type: "text", text: "Missing required argument: source" }],
          };
        }
        const result = rustledger.balances(source);
        if (result.errors?.length > 0) {
          return {
            isError: true,
            content: [{ type: "text", text: formatErrors(result.errors) }],
          };
        }
        return {
          content: [{ type: "text", text: formatQueryResult(result) }],
        };
      }

      case "format": {
        const source = args?.source as string;
        if (!source) {
          return {
            isError: true,
            content: [{ type: "text", text: "Missing required argument: source" }],
          };
        }
        const result = rustledger.format(source);
        if (result.errors?.length > 0) {
          return {
            isError: true,
            content: [{ type: "text", text: formatErrors(result.errors) }],
          };
        }
        return {
          content: [{ type: "text", text: result.formatted || "" }],
        };
      }

      case "parse": {
        const source = args?.source as string;
        if (!source) {
          return {
            isError: true,
            content: [{ type: "text", text: "Missing required argument: source" }],
          };
        }
        const result = rustledger.parse(source);
        if (result.errors?.length > 0) {
          return {
            isError: true,
            content: [{ type: "text", text: formatErrors(result.errors) }],
          };
        }
        return {
          content: [
            {
              type: "text",
              text: JSON.stringify(result.ledger, null, 2),
            },
          ],
        };
      }

      case "completions": {
        const partialQuery = args?.partial_query as string;
        const cursorPos = args?.cursor_pos as number;
        if (partialQuery === undefined || cursorPos === undefined) {
          return {
            isError: true,
            content: [
              {
                type: "text",
                text: "Missing required arguments: partial_query and cursor_pos",
              },
            ],
          };
        }
        const result = rustledger.bqlCompletions(partialQuery, cursorPos);
        return {
          content: [{ type: "text", text: JSON.stringify(result, null, 2) }],
        };
      }

      case "list_plugins": {
        const plugins = rustledger.listPlugins();
        return {
          content: [{ type: "text", text: JSON.stringify(plugins, null, 2) }],
        };
      }

      case "run_plugin": {
        const source = args?.source as string;
        const pluginName = args?.plugin_name as string;
        if (!source || !pluginName) {
          return {
            isError: true,
            content: [
              {
                type: "text",
                text: "Missing required arguments: source and plugin_name",
              },
            ],
          };
        }
        const result = rustledger.runPlugin(source, pluginName);
        if (result.errors?.length > 0) {
          return {
            isError: true,
            content: [{ type: "text", text: formatErrors(result.errors) }],
          };
        }
        return {
          content: [
            {
              type: "text",
              text: `Plugin processed ${result.directives.length} directives.`,
            },
          ],
        };
      }

      default:
        return {
          isError: true,
          content: [{ type: "text", text: `Unknown tool: ${name}` }],
        };
    }
  } catch (error) {
    return {
      isError: true,
      content: [
        {
          type: "text",
          text: `Error: ${error instanceof Error ? error.message : String(error)}`,
        },
      ],
    };
  }
});

// Resources
const RESOURCES = [
  {
    uri: "rustledger://docs/bql",
    name: "BQL Query Language Reference",
    description: "Documentation for Beancount Query Language",
    mimeType: "text/markdown",
  },
];

server.setRequestHandler(ListResourcesRequestSchema, async () => {
  return { resources: RESOURCES };
});

server.setRequestHandler(ReadResourceRequestSchema, async (request) => {
  const { uri } = request.params;

  if (uri === "rustledger://docs/bql") {
    return {
      contents: [
        {
          uri,
          mimeType: "text/markdown",
          text: BQL_DOCS,
        },
      ],
    };
  }

  throw new Error(`Unknown resource: ${uri}`);
});

// Helper functions
interface BeancountError {
  message: string;
  line?: number;
  column?: number;
  severity: "error" | "warning";
}

function formatErrors(errors: BeancountError[]): string {
  return errors
    .map((e) => {
      const loc = e.line ? `:${e.line}${e.column ? `:${e.column}` : ""}` : "";
      return `[${e.severity}]${loc} ${e.message}`;
    })
    .join("\n");
}

interface QueryResult {
  columns: string[];
  rows: unknown[][];
}

function formatQueryResult(result: QueryResult): string {
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

function formatCell(value: unknown): string {
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
      const inv = value as { positions: Array<{ units: { number: string; currency: string } }> };
      return inv.positions
        .map((p) => `${p.units.number} ${p.units.currency}`)
        .join(", ");
    }
    return JSON.stringify(value);
  }
  return String(value);
}

// BQL Documentation
const BQL_DOCS = `# BQL - Beancount Query Language

BQL is a SQL-like query language for querying Beancount ledgers.

## Basic Syntax

\`\`\`sql
SELECT [DISTINCT] <target-spec>, ...
[FROM <from-spec>]
[WHERE <where-expression>]
[GROUP BY <group-spec>, ...]
[ORDER BY <order-spec>, ...]
[LIMIT <limit>]
\`\`\`

## Common Queries

### Account Balances
\`\`\`sql
BALANCES
-- or equivalently:
SELECT account, sum(position) GROUP BY account
\`\`\`

### Filter by Account
\`\`\`sql
SELECT date, narration, position
WHERE account ~ "Expenses:Food"
\`\`\`

### Filter by Date Range
\`\`\`sql
SELECT date, account, position
WHERE date >= 2024-01-01 AND date < 2024-02-01
\`\`\`

### Monthly Summary
\`\`\`sql
SELECT year(date), month(date), sum(position)
WHERE account ~ "Expenses"
GROUP BY year(date), month(date)
ORDER BY year(date), month(date)
\`\`\`

### Journal Entries
\`\`\`sql
JOURNAL "Assets:Checking"
\`\`\`

## Available Functions

- \`year(date)\`, \`month(date)\`, \`day(date)\` - Extract date parts
- \`sum(position)\` - Sum positions
- \`count()\` - Count entries
- \`first(x)\`, \`last(x)\` - First/last values
- \`min(x)\`, \`max(x)\` - Min/max values

## Operators

- \`~\` - Regex match (e.g., \`account ~ "Expenses:.*"\`)
- \`=\`, \`!=\`, \`<\`, \`>\`, \`<=\`, \`>=\` - Comparisons
- \`AND\`, \`OR\`, \`NOT\` - Boolean operators
`;

// Start the server
async function main() {
  const transport = new StdioServerTransport();
  await server.connect(transport);
  // Log to stderr to avoid interfering with MCP protocol on stdout
  console.error(`rustledger MCP server v${rustledger.version()} started`);
}

main().catch((error) => {
  console.error("Fatal error:", error);
  process.exit(1);
});
