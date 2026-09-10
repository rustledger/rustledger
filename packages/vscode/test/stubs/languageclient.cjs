// Stand-in for `vscode-languageclient/node`.
//
// Faithful in the one respect that matters: the base class registers builtin
// features from its CONSTRUCTOR (as `registerBuiltinFeatures` really does), and
// the executeCommand feature registers each advertised id through
// `vscode.commands.registerCommand` with no existence check, which is precisely
// what throws on the second client in a multi-root workspace.
//
// Without that, a test asserting "no collision" would only be exercising the
// extension's own code and would pass with the fix removed.
const vscode = require("./vscode.cjs");

class LanguageClient {
  constructor(id, name, serverOptions, clientOptions) {
    this.id = id;
    this.name = name;
    this.serverOptions = serverOptions;
    this.clientOptions = clientOptions;
    this.accepted = [];
    this.sent = [];
    this.initializeResult = undefined;
    // Dispatches to the SUBCLASS override, exactly as the real constructor
    // does, so the ordering under test is the real one.
    this.registerBuiltinFeatures();
  }

  registerBuiltinFeatures() {
    this.registerFeature({
      registrationType: { method: "workspace/executeCommand" },
      initialize: (capabilities) => {
        for (const command of capabilities?.executeCommandProvider?.commands ??
          []) {
          // No existence check and no try/catch, same as the library.
          vscode.commands.registerCommand(command, () => {});
        }
      },
    });
    this.registerFeature({
      registrationType: { method: "textDocument/hover" },
      initialize() {},
    });
  }

  registerFeature(feature) {
    this.accepted.push(feature);
  }

  async sendRequest(type, params) {
    this.sent.push({ type, params });
    return { ok: this.id };
  }

  // `initializeFeatures` in the real client; this is where the throw happens.
  async start() {
    for (const feature of this.accepted) {
      feature.initialize?.(this.initializeResult?.capabilities);
    }
  }

  async stop() {}
}

module.exports = {
  LanguageClient,
  ExecuteCommandRequest: {
    method: "workspace/executeCommand",
    type: { method: "workspace/executeCommand" },
  },
};
