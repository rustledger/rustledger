// Minimal `vscode` stand-in: only what extension.ts touches in the paths under
// test. Anything else is deliberately absent so a test that strays into
// untested territory fails loudly rather than silently passing on a mock.
const registered = new Map();
let activeUri;

class Uri {
  constructor(fsPath) {
    this.fsPath = fsPath;
  }
  static file(p) {
    return new Uri(p);
  }
  static parse(value) {
    if (typeof value !== "string" || !value.startsWith("file://")) {
      throw new Error(`not a uri: ${value}`);
    }
    return new Uri(value.slice("file://".length));
  }
  toString() {
    return `file://${this.fsPath}`;
  }
}

module.exports = {
  Uri,
  RelativePattern: class {
    constructor(base, pattern) {
      this.base = base;
      this.pattern = pattern;
    }
  },
  Disposable: class {
    constructor(fn) {
      this.dispose = fn;
    }
  },
  commands: {
    registerCommand(id, handler) {
      if (registered.has(id)) {
        // VS Code's real behavior, and the whole bug: a duplicate throws.
        throw new Error(`command '${id}' already exists`);
      }
      registered.set(id, handler);
      return { dispose: () => registered.delete(id) };
    },
  },
  window: {
    get activeTextEditor() {
      return activeUri ? { document: { uri: activeUri } } : undefined;
    },
    createOutputChannel: () => ({ appendLine() {} }),
  },
  workspace: {
    workspaceFolders: [],
    getWorkspaceFolder(uri) {
      const folders = module.exports.workspace.workspaceFolders ?? [];
      return folders.find((f) => uri.fsPath.startsWith(`${f.uri.fsPath}/`));
    },
    createFileSystemWatcher: () => ({ dispose() {} }),
    getConfiguration: () => ({ get: (_k, d) => d }),
  },
  __harness: {
    registered,
    setActive(uri) {
      activeUri = uri;
    },
    reset() {
      registered.clear();
      activeUri = undefined;
      module.exports.workspace.workspaceFolders = [];
    },
  },
};
