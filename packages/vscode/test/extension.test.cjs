// Tests for the multi-root command-collision fix (#2287).
//
// In a multi-root workspace only the first language server started: every
// client registered the same server-advertised command ids globally, and the
// second threw `command 'rledger.insertDate' already exists` during
// `initializeFeatures`, so that folder got no diagnostics at all.
//
// The real failure needs two workspace folders in a live extension host. What
// is testable here is the decision-making, against a `vscode` stub whose
// `registerCommand` throws on a duplicate exactly as the real one does.

const assert = require("node:assert/strict");
const test = require("node:test");
const path = require("node:path");
const Module = require("node:module");

const STUB_VSCODE = require.resolve("./stubs/vscode.cjs");
const STUB_CLIENT = require.resolve("./stubs/languageclient.cjs");

const originalLoad = Module._load;
Module._load = function (request, parent, isMain) {
  if (request === "vscode") {
    return originalLoad.call(this, STUB_VSCODE, parent, isMain);
  }
  if (request === "vscode-languageclient/node") {
    return originalLoad.call(this, STUB_CLIENT, parent, isMain);
  }
  return originalLoad.call(this, request, parent, isMain);
};

const vscode = require(STUB_VSCODE);
const { LanguageClient, ExecuteCommandRequest } = require(STUB_CLIENT);
const { __test } = require(path.join(__dirname, "..", "out", "extension.test.cjs"));
const { SingleCommandOwnerClient, registerServerCommands, commandTargetUri, clients, serverCommands } = __test;

function reset() {
  vscode.__harness.reset();
  clients.clear();
  serverCommands.clear();
}

function clientFor(rootPath, commands) {
  const client = new SingleCommandOwnerClient(`rustledger:${rootPath}`, "rustledger", {}, {});
  client.initializeResult = {
    capabilities: { executeCommandProvider: { commands } },
  };
  clients.set(`file://${rootPath}`, client);
  return client;
}

const COMMANDS = [
  "rledger.insertDate",
  "rledger.sortTransactions",
  "rledger.alignAmounts",
  "rledger.showAccountBalance",
  "rledger.noop",
];

test("the executeCommand feature is declined and every other feature passes through", () => {
  reset();
  // The base constructor registers the builtins, so this already reflects the
  // subclass's filtering by the time it returns.
  const client = new SingleCommandOwnerClient("id", "rustledger", {}, {});
  const methods = () =>
    client.accepted.map((f) => f.registrationType?.method ?? "<static>");

  assert.ok(
    !methods().includes("workspace/executeCommand"),
    `the executeCommand builtin must be declined; accepted ${methods()}`,
  );
  assert.ok(
    methods().includes("textDocument/hover"),
    `every other builtin must survive; accepted ${methods()}`,
  );

  // A static feature has no registrationType at all and must not be mistaken
  // for the one being declined.
  const staticFeature = { fillClientCapabilities() {} };
  client.registerFeature(staticFeature);
  assert.ok(
    client.accepted.includes(staticFeature),
    "a feature without a registrationType must pass through",
  );
});

test("a second client starts instead of dying on duplicate command ids", async () => {
  reset();
  const a = clientFor("/w/ledger-a", COMMANDS);
  const b = clientFor("/w/ledger-b", COMMANDS);

  // `start` runs the features, which is where the real client threw
  // `command 'rledger.insertDate' already exists` and left folder B with no
  // server at all. The stub's base class registers the ids the same way, so
  // this fails if the feature is not declined.
  await a.start();
  await b.start();

  registerServerCommands(a);
  registerServerCommands(b);

  assert.deepEqual([...serverCommands.keys()].sort(), [...COMMANDS].sort());
  assert.equal(
    vscode.__harness.registered.size,
    COMMANDS.length,
    "each id must be registered exactly once for the window",
  );
});

test("a command is answered by the client that owns the document", async () => {
  reset();
  const a = clientFor("/w/ledger-a", COMMANDS);
  const b = clientFor("/w/ledger-b", COMMANDS);
  vscode.workspace.workspaceFolders = [
    { uri: vscode.Uri.file("/w/ledger-a") },
    { uri: vscode.Uri.file("/w/ledger-b") },
  ];
  registerServerCommands(a);
  registerServerCommands(b);

  const handler = vscode.__harness.registered.get("rledger.showAccountBalance");
  await handler({ uri: "file:///w/ledger-b/ledger/2025-01.beancount" });

  assert.equal(a.sent.length, 0, "the wrong ledger's server must not answer");
  assert.equal(b.sent.length, 1);
  assert.equal(b.sent[0].params.command, "rledger.showAccountBalance");
});

test("with no argument uri, the active editor decides the owner", async () => {
  reset();
  const a = clientFor("/w/ledger-a", COMMANDS);
  const b = clientFor("/w/ledger-b", COMMANDS);
  vscode.workspace.workspaceFolders = [
    { uri: vscode.Uri.file("/w/ledger-a") },
    { uri: vscode.Uri.file("/w/ledger-b") },
  ];
  registerServerCommands(a);
  registerServerCommands(b);
  vscode.__harness.setActive(vscode.Uri.file("/w/ledger-b/ledger/2025-01.beancount"));

  await vscode.__harness.registered.get("rledger.insertDate")();

  assert.equal(a.sent.length, 0);
  assert.equal(b.sent.length, 1);
});

test("an argument uri beats the active editor", () => {
  reset();
  vscode.__harness.setActive(vscode.Uri.file("/w/ledger-a/x.beancount"));
  const target = commandTargetUri([{ uri: "file:///w/ledger-b/y.beancount" }]);
  assert.equal(target.fsPath, "/w/ledger-b/y.beancount");
});

test("a stopped owner falls back to a running client rather than doing nothing", async () => {
  reset();
  const a = clientFor("/w/ledger-a", COMMANDS);
  registerServerCommands(a);
  vscode.workspace.workspaceFolders = [{ uri: vscode.Uri.file("/w/ledger-a") }];

  // A file no client owns: a folder removed, or a scratch file elsewhere.
  await vscode.__harness.registered.get("rledger.insertDate")({
    uri: "file:///elsewhere/scratch.beancount",
  });

  assert.equal(a.sent.length, 1, "the only running server should still answer");
});
