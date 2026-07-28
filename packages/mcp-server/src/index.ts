#!/usr/bin/env node

import { readFileSync } from "fs";
import { createRequire } from "module";
import { StdioServerTransport } from "@modelcontextprotocol/server/stdio";
import { Server } from "@modelcontextprotocol/server";
import { initSync } from "@rustledger/wasm";
import * as rustledger from "@rustledger/wasm";

// Import modular components
import { TOOLS } from "./tools.js";
import { handleToolCall } from "./handlers.js";
import { RESOURCES, getResourceContents } from "./resources.js";
import { PROMPTS, getPrompt } from "./prompts.js";
import type { ToolArguments } from "./types.js";

// Initialize WASM synchronously for Node.js
// (The --target web build uses fetch() which doesn't work in Node.js)
const require = createRequire(import.meta.url);
const wasmPath = require.resolve("@rustledger/wasm/rustledger_wasm_bg.wasm");
initSync(readFileSync(wasmPath));
rustledger.init();

// Start the server
async function main(): Promise<void> {

  // Create server instance
  const server = new Server(
    {
      name: "rustledger",
      version: rustledger.version(),
    },
    {
      capabilities: {
        tools: {},
        resources: {},
        prompts: {},
      },
    }
  );

  // List available tools
  server.setRequestHandler("tools/list", async () => {
    return { tools: TOOLS };
  });

  // Handle tool calls
  server.setRequestHandler("tools/call", async (request) => {
    const { name, arguments: args } = request.params;

    try {
      return handleToolCall(name, args as ToolArguments | undefined);
    } catch (error) {
      return {
        isError: true,
        content: [
          {
            type: "text" as const,
            text: `Error: ${error instanceof Error ? error.message : String(error)}`,
          },
        ],
      };
    }
  });

  // List available resources
  server.setRequestHandler("resources/list", async () => {
    return { resources: RESOURCES };
  });

  // Read resource contents
  server.setRequestHandler("resources/read", async (request) => {
    const { uri } = request.params;
    const contents = getResourceContents(uri);

    if (!contents) {
      throw new Error(`Unknown resource: ${uri}`);
    }

    return { contents: [contents] };
  });

  // List available prompts
  server.setRequestHandler("prompts/list", async () => {
    return { prompts: PROMPTS };
  });

  // Get prompt content
  server.setRequestHandler("prompts/get", async (request) => {
    const { name, arguments: args } = request.params;
    return getPrompt(name, args);
  });

  const transport = new StdioServerTransport();
  await server.connect(transport);
  console.error(`rustledger MCP server v${rustledger.version()} started`);
}

main().catch((error) => {
  console.error("Fatal error:", error);
  process.exit(1);
});
