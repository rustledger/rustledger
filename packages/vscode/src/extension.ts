import { execFileSync } from "child_process";
import { createWriteStream } from "fs";
import { get } from "https";
import { tmpdir } from "os";
import { join } from "path";
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

let client: LanguageClient | undefined;
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

async function startClient(context: vscode.ExtensionContext): Promise<boolean> {
  const config = vscode.workspace.getConfiguration("rustledger");
  const command = config.get<string>("server.path", "rledger-lsp");
  const extraArgs = config.get<string[]>("server.extraArgs", []);
  const journalFile = config.get<string>("journalFile", "");

  if (!findBinary(command)) {
    const install = "Install";
    const result = await vscode.window.showWarningMessage(
      `Could not find "${command}". Install rustledger to enable language features.`,
      install,
    );
    if (result === install) {
      vscode.env.openExternal(vscode.Uri.parse(INSTALL_URL));
    }
    return false;
  }

  const serverOptions: ServerOptions = {
    command,
    args: extraArgs,
  };

  const initializationOptions: Record<string, string> = {};
  if (journalFile) {
    initializationOptions.journalFile = journalFile;
  }

  const clientOptions: LanguageClientOptions = {
    documentSelector: [{ scheme: "file", language: "beancount" }],
    synchronize: {
      fileEvents:
        vscode.workspace.createFileSystemWatcher("**/*.{beancount,bean}"),
    },
    initializationOptions,
    outputChannel,
  };

  client = new LanguageClient(
    "rustledger",
    "rustledger",
    serverOptions,
    clientOptions,
  );

  await client.start();
  outputChannel?.appendLine(`Started rledger-lsp: ${command}`);
  return true;
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
      if (client) {
        await client.stop();
        client = undefined;
      }
      await startClient(context);
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

  // Start the client
  const started = await startClient(context);
  if (started) {
    context.subscriptions.push({
      dispose: () => {
        client?.stop();
      },
    });
  }

  // Check for updates in background (don't await) if enabled
  const config = vscode.workspace.getConfiguration("rustledger");
  if (config.get<boolean>("checkForUpdates", true)) {
    checkForUpdates(context);
  }
}

export async function deactivate(): Promise<void> {
  await client?.stop();
  client = undefined;
}
