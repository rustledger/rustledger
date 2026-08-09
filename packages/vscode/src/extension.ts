import { execFileSync } from "child_process";
import { createWriteStream } from "fs";
import { get } from "https";
import { tmpdir } from "os";
import { dirname, join } from "path";
import * as vscode from "vscode";
import {
  LanguageClient,
  LanguageClientOptions,
  ServerOptions,
} from "vscode-languageclient/node";

const INSTALL_URL =
  "https://rustledger.github.io/getting-started/installation.html";
const GITHUB_API_URL =
  "https://api.github.com/repos/rustledger/rustledger/releases/latest";
const VSIX_ASSET_NAME = "rustledger-vscode.vsix";

// One client per ledger root, keyed by that root's URI string.
//
// Multi-root workspaces hold independent ledgers (#1974): two folders with
// their own `main.beancount` share nothing, so they get a server each. That
// also means the SERVER needs no change — `rledger-lsp` reads
// `workspace_folders.first()` and holds one ledger, which is exactly right
// once each process is given exactly one folder.
const clients = new Map<string, LanguageClient>();
// Created with `{ log: true }` below, so it's a LogOutputChannel — which is
// also what vscode-languageclient v10's LanguageClientOptions.outputChannel
// requires (v9 accepted a plain OutputChannel).
let outputChannel: vscode.LogOutputChannel | undefined;

function findBinary(command: string): boolean {
  try {
    execFileSync(command, ["--version"], { stdio: "ignore" });
    return true;
  } catch {
    return false;
  }
}

interface GitHubRelease {
  tag_name: string;
  assets: { name: string; browser_download_url: string }[];
}

function compareVersions(current: string, latest: string): number {
  const parse = (v: string) => v.replace(/^v/, "").split(".").map(Number);
  const [a, b] = [parse(current), parse(latest)];
  for (let i = 0; i < Math.max(a.length, b.length); i++) {
    const diff = (a[i] || 0) - (b[i] || 0);
    if (diff !== 0) return diff;
  }
  return 0;
}

async function fetchJson<T>(url: string): Promise<T> {
  return new Promise((resolve, reject) => {
    get(url, { headers: { "User-Agent": "rustledger-vscode" } }, (res) => {
      if (res.statusCode === 301 || res.statusCode === 302) {
        fetchJson<T>(res.headers.location!).then(resolve).catch(reject);
        return;
      }
      if (res.statusCode !== 200) {
        reject(new Error(`HTTP ${res.statusCode}`));
        return;
      }
      let data = "";
      res.on("data", (chunk) => (data += chunk));
      res.on("end", () => {
        try {
          resolve(JSON.parse(data));
        } catch (e) {
          reject(new Error(`Invalid JSON response: ${e}`));
        }
      });
      res.on("error", reject);
    }).on("error", reject);
  });
}

async function downloadFile(url: string, dest: string): Promise<void> {
  return new Promise((resolve, reject) => {
    get(url, { headers: { "User-Agent": "rustledger-vscode" } }, (res) => {
      if (res.statusCode === 301 || res.statusCode === 302) {
        downloadFile(res.headers.location!, dest).then(resolve).catch(reject);
        return;
      }
      if (res.statusCode !== 200) {
        reject(new Error(`HTTP ${res.statusCode}`));
        return;
      }
      const file = createWriteStream(dest);
      res.pipe(file);
      file.on("finish", () => {
        file.close();
        resolve();
      });
      file.on("error", reject);
    }).on("error", reject);
  });
}

async function checkForUpdates(
  context: vscode.ExtensionContext,
): Promise<void> {
  try {
    const currentVersion = context.extension.packageJSON.version;
    const release = await fetchJson<GitHubRelease>(GITHUB_API_URL);
    const latestVersion = release.tag_name.replace(/^v/, "");

    if (compareVersions(currentVersion, latestVersion) >= 0) {
      outputChannel?.appendLine(
        `Extension is up to date (v${currentVersion})`,
      );
      return;
    }

    const vsixAsset = release.assets.find((a) => a.name === VSIX_ASSET_NAME);
    if (!vsixAsset) {
      outputChannel?.appendLine(
        `Update available (v${latestVersion}) but vsix not found in release`,
      );
      return;
    }

    const update = "Update";
    const dismiss = "Dismiss";
    const result = await vscode.window.showInformationMessage(
      `rustledger extension v${latestVersion} is available (current: v${currentVersion})`,
      update,
      dismiss,
    );

    if (result === update) {
      await vscode.window.withProgress(
        {
          location: vscode.ProgressLocation.Notification,
          title: "Updating rustledger extension...",
          cancellable: false,
        },
        async () => {
          const vsixPath = join(tmpdir(), VSIX_ASSET_NAME);
          outputChannel?.appendLine(`Downloading ${vsixAsset.browser_download_url}`);
          await downloadFile(vsixAsset.browser_download_url, vsixPath);
          outputChannel?.appendLine(`Installing from ${vsixPath}`);
          await vscode.commands.executeCommand(
            "workbench.extensions.installExtension",
            vscode.Uri.file(vsixPath),
          );
          const reload = "Reload";
          const later = "Later";
          const reloadResult = await vscode.window.showInformationMessage(
            `rustledger extension updated to v${latestVersion}. Reload to activate.`,
            reload,
            later,
          );
          if (reloadResult === reload) {
            await vscode.commands.executeCommand("workbench.action.reloadWindow");
          }
        },
      );
    }
  } catch (error) {
    outputChannel?.appendLine(`Update check failed: ${error}`);
  }
}

// The ledger root a document belongs to.
//
// Its workspace folder when it has one. When it does not — a `.beancount`
// file opened with no workspace, or from outside every folder — its own
// directory stands in.
//
// A directory rather than one catch-all client with an unrestricted selector:
// selectors have no "everything except" form, so a broad fallback would also
// claim files already owned by a folder client and both servers would answer.
// Rooting on the containing directory keeps every selector disjoint by
// construction, and it preserves what single-file users have today.
function rootFor(uri: vscode.Uri): {
  root: vscode.Uri;
  folder: vscode.WorkspaceFolder | undefined;
} {
  const folder = vscode.workspace.getWorkspaceFolder(uri);
  if (folder) {
    return { root: folder.uri, folder };
  }
  return { root: vscode.Uri.file(dirname(uri.fsPath)), folder: undefined };
}

// Whether each configured binary is present, keyed BY COMMAND.
//
// Asked once per command rather than once per client, so N folders sharing a
// server path produce one missing-binary popup instead of N. Keyed rather than
// a single flag because `server.path` is readable per-resource: two folders can
// name different binaries, and caching the first answer for the second would
// report a missing binary as present, or warn about the wrong one.
const binaryChecks = new Map<string, boolean>();

async function ensureBinary(command: string): Promise<boolean> {
  const cached = binaryChecks.get(command);
  if (cached !== undefined) {
    return cached;
  }
  // Recorded BEFORE awaiting the popup: `findBinary` is synchronous, so a
  // concurrent caller that arrives while the dialog is open reads the cached
  // answer and does not raise a second one.
  const present = findBinary(command);
  binaryChecks.set(command, present);
  if (!present) {
    const install = "Install";
    const result = await vscode.window.showWarningMessage(
      `Could not find "${command}". Install rustledger to enable language features.`,
      install,
    );
    if (result === install) {
      vscode.env.openExternal(vscode.Uri.parse(INSTALL_URL));
    }
  }
  return present;
}

// Start a client for one ledger root, unless one is already running for it.
// Starts in flight, so a second caller for the same root joins the first
// rather than racing it.
const starting = new Map<string, Promise<void>>();

async function startClientForRoot(
  root: vscode.Uri,
  folder: vscode.WorkspaceFolder | undefined,
): Promise<void> {
  const key = root.toString();
  if (clients.has(key)) {
    return;
  }
  // The `clients` check alone is not enough, which Copilot caught: this
  // function awaits before it records anything, so two documents from the SAME
  // folder — exactly what `startClientsForOpenDocuments` produces via
  // `Promise.all` — both passed the guard and started a server each.
  // Reproduced at 2 servers for one folder.
  //
  // Reserving the in-flight promise closes it because the reservation happens
  // in the same synchronous turn as the lookup: no other task can interleave
  // between the `get` and the `set`.
  const inFlight = starting.get(key);
  if (inFlight) {
    return inFlight;
  }
  const attempt = startClientForRootUncontended(root, folder, key);
  starting.set(key, attempt);
  try {
    await attempt;
  } finally {
    starting.delete(key);
  }
}

async function startClientForRootUncontended(
  root: vscode.Uri,
  folder: vscode.WorkspaceFolder | undefined,
  key: string,
): Promise<void> {
  // Read config against the ROOT, which is what makes a folder-level
  // `.vscode/settings.json` take effect. Without the resource argument this
  // returns the window value and every folder gets the same journal.
  const config = vscode.workspace.getConfiguration("rustledger", root);
  const command = config.get<string>("server.path", "rledger-lsp");
  const extraArgs = config.get<string[]>("server.extraArgs", []);
  const journalFile = config.get<string>("journalFile", "");

  if (!(await ensureBinary(command))) {
    return;
  }

  const serverOptions: ServerOptions = { command, args: extraArgs };

  const initializationOptions: Record<string, string> = {};
  if (journalFile) {
    // Left RELATIVE on purpose when the user wrote it that way. The server
    // resolves a relative journal against its workspace root
    // (`resolve_explicit_journal`), so the same `ledger/main.beancount` in two
    // folders' settings resolves to two different files — which is the whole
    // point of the request.
    initializationOptions.journalFile = journalFile;
  }

  // Scope the selector to this root so exactly one client claims each file.
  //
  // Two spellings of the same pattern, because the two consumers take
  // different types: `createFileSystemWatcher` wants VS Code's
  // `RelativePattern` (whose `baseUri` is a `Uri`), while a
  // `DocumentFilter.pattern` is the LSP protocol's, whose `baseUri` is a
  // string. Passing the VS Code one to the selector does not type-check.
  // RECURSIVE for a workspace folder, whose ledger legitimately spans
  // subdirectories. NON-recursive for an ad-hoc directory root, and that
  // difference is load-bearing rather than cosmetic.
  //
  // An ad-hoc root can CONTAIN workspace folders: open `/w/notes.beancount`
  // while `/w/HK` and `/w/CA` are the folders, and a recursive `/w` selector
  // also matches every file those two own — two clients claiming the same
  // document, two sets of diagnostics. Verified by enumerating owners per
  // file: recursive gives 2 owners for each folder file, non-recursive gives
  // exactly 1 for every file.
  //
  // The cost is that a file outside every folder gets a client per DIRECTORY
  // rather than per tree. Only reachable for files no workspace folder owns,
  // and preferable to one document answered twice.
  const glob = folder
    ? "**/*.{beancount,bean}"
    : "*.{beancount,bean}";
  const watcherPattern = new vscode.RelativePattern(root, glob);
  const clientOptions: LanguageClientOptions = {
    documentSelector: [
      {
        scheme: "file",
        language: "beancount",
        pattern: { baseUri: root.toString(), pattern: glob },
      },
    ],
    synchronize: {
      fileEvents: vscode.workspace.createFileSystemWatcher(watcherPattern),
    },
    initializationOptions,
    outputChannel,
    // Makes the client report THIS folder in `workspaceFolders`, so the
    // server's `folders.first()` resolves the intended root rather than
    // whichever folder happens to sort first in the window.
    workspaceFolder: folder,
  };

  // A distinct id per client: vscode-languageclient uses it for the output
  // channel and for `client.stop()` bookkeeping, and reusing one id across
  // clients makes the second silently shadow the first.
  const client = new LanguageClient(
    `rustledger:${key}`,
    "rustledger",
    serverOptions,
    clientOptions,
  );
  clients.set(key, client);

  try {
    await client.start();
  } catch (error) {
    // Registered before starting so a concurrent caller sees it, which means a
    // FAILED start would otherwise leave a dead client in the map — and
    // `clients.has(key)` then makes every later attempt a no-op, disabling that
    // folder until the window is reloaded. A spawn failure is usually
    // transient (binary mid-upgrade, a bad `server.path` since corrected), so
    // it must not be permanent.
    clients.delete(key);
    outputChannel?.appendLine(`Failed to start rledger-lsp for ${key}: ${error}`);
    return;
  }
  outputChannel?.appendLine(
    `Started rledger-lsp for ${key}` +
      (journalFile ? ` (journalFile: ${journalFile})` : " (auto-discovery)"),
  );
}

// Start a client for a document's root if it does not have one yet.
async function ensureClientForDocument(
  document: vscode.TextDocument,
): Promise<void> {
  if (document.languageId !== "beancount" || document.uri.scheme !== "file") {
    return;
  }
  const { root, folder } = rootFor(document.uri);
  await startClientForRoot(root, folder);
}

async function stopClient(key: string): Promise<void> {
  // Wait for an in-flight start first. Removing a workspace folder while its
  // server is still coming up would otherwise find nothing in `clients`,
  // return, and let the start finish afterwards — leaving a server running for
  // a folder that is gone.
  await starting.get(key)?.catch(() => undefined);

  const client = clients.get(key);
  if (!client) {
    return;
  }
  clients.delete(key);
  await client.stop();
  outputChannel?.appendLine(`Stopped rledger-lsp for ${key}`);
}

async function stopAllClients(): Promise<void> {
  await Promise.all([...clients.keys()].map(stopClient));
}

// Start clients for every beancount document already open.
//
// Activation happens on the first such document, but a window restored with
// several open across several folders needs one client each — waiting for a
// fresh `onDidOpenTextDocument` would leave all but one without features.
async function startClientsForOpenDocuments(): Promise<void> {
  await Promise.all(
    vscode.workspace.textDocuments.map(ensureClientForDocument),
  );
}

export async function activate(
  context: vscode.ExtensionContext,
): Promise<void> {
  // Create output channel first so it's available for logging
  outputChannel = vscode.window.createOutputChannel("rustledger", {
    log: true,
  });
  context.subscriptions.push(outputChannel);

  // Register restart command
  const restartCommand = vscode.commands.registerCommand(
    "rustledger.restartServer",
    async () => {
      outputChannel?.appendLine("Restarting rledger-lsp...");
      await stopAllClients();
      // Re-ask for the binaries: a restart is how a user retries after
      // installing one, and a cached "missing" would make that do nothing.
      binaryChecks.clear();
      await startClientsForOpenDocuments();
    },
  );
  context.subscriptions.push(restartCommand);

  // Register check for updates command
  const updateCommand = vscode.commands.registerCommand(
    "rustledger.checkForUpdates",
    async () => {
      outputChannel?.appendLine("Checking for updates...");
      await checkForUpdates(context);
    },
  );
  context.subscriptions.push(updateCommand);

  // A document opened later may belong to a root with no client yet — a second
  // folder's ledger, or a file outside the workspace entirely.
  context.subscriptions.push(
    vscode.workspace.onDidOpenTextDocument(ensureClientForDocument),
  );

  // Folder added or removed. Removal must stop that folder's server; addition
  // is handled when one of its documents opens.
  context.subscriptions.push(
    vscode.workspace.onDidChangeWorkspaceFolders(async (event) => {
      await Promise.all(
        event.removed.map((folder) => stopClient(folder.uri.toString())),
      );
      await startClientsForOpenDocuments();
    }),
  );

  // Settings changed. `journalFile` reaches the server only through
  // `initializationOptions`, which is sent once at startup, so the client for
  // an affected root has to be restarted rather than notified.
  //
  // Before this, changing `journalFile` did nothing until the user found the
  // restart command — true single-root as well, just less visible.
  context.subscriptions.push(
    vscode.workspace.onDidChangeConfiguration(async (event) => {
      const affected = [...clients.keys()].filter((key) =>
        event.affectsConfiguration("rustledger", vscode.Uri.parse(key)),
      );
      if (affected.length === 0) {
        return;
      }
      outputChannel?.appendLine(
        `Configuration changed; restarting ${affected.length} server(s)`,
      );
      await Promise.all(affected.map(stopClient));
      // `server.path` may be what changed.
      binaryChecks.clear();
      await startClientsForOpenDocuments();
    }),
  );

  context.subscriptions.push({ dispose: () => void stopAllClients() });

  await startClientsForOpenDocuments();

  // Check for updates in background (don't await) if enabled
  const config = vscode.workspace.getConfiguration("rustledger");
  if (config.get<boolean>("checkForUpdates", true)) {
    checkForUpdates(context);
  }
}

export async function deactivate(): Promise<void> {
  await stopAllClients();
}
