import * as fs from "fs";
import * as os from "os";
import * as path from "path";

import axios from "axios";
import * as vscode from "vscode";
import {
  CloseAction,
  ErrorAction,
  Executable,
  LanguageClient,
  LanguageClientOptions,
  ServerOptions,
  State,
} from "vscode-languageclient/node";

import { Assistant } from "./assistant";

let client: LanguageClient;

let outputChannel: vscode.OutputChannel | undefined;

function log(message: string) {
  if (outputChannel === undefined) {
    outputChannel = vscode.window.createOutputChannel("Acorn Extension");
  }
  outputChannel.appendLine(message);
}

/**
 * Downloads a file from the given URL and saves it to the specified path.
 * Downloads to a temporary file first, then atomically renames on success.
 * This prevents partial downloads from being treated as valid binaries.
 * @param url - The URL to download from.
 * @param filePath - The full path where the file will be saved.
 */
async function downloadFile(url: string, filePath: string): Promise<void> {
  const tempPath = filePath + ".tmp";

  // Clean up any existing temp file from a previous failed download
  try {
    if (fs.existsSync(tempPath)) {
      fs.unlinkSync(tempPath);
    }
  } catch (err) {
    console.warn("failed to clean up old temp file:", err);
  }

  let response = await axios.get(url, { responseType: "stream" });

  let fileStream = fs.createWriteStream(tempPath);

  return new Promise((resolve, reject) => {
    const cleanup = (err?: Error) => {
      // Clean up temp file on error
      fs.unlink(tempPath, (unlinkErr) => {
        if (unlinkErr && unlinkErr.code !== "ENOENT") {
          console.error("failed to clean up temp file:", unlinkErr);
        }
        if (err) {
          reject(err);
        }
      });
    };

    response.data.pipe(fileStream);

    // Handle successful completion
    fileStream.on("finish", () => {
      // Atomically rename temp file to final destination
      fs.rename(tempPath, filePath, (err) => {
        if (err) {
          cleanup(err);
        } else {
          resolve();
        }
      });
    });

    // Handle file stream errors
    fileStream.on("error", (err) => {
      cleanup(err);
    });

    // Handle network/stream errors from axios
    response.data.on("error", (err) => {
      fileStream.destroy(); // Stop writing
      cleanup(err);
    });
  });
}

function makeCheck(color: string): vscode.Uri {
  let svg = `
  <svg xmlns="http://www.w3.org/2000/svg" viewBox="0 0 16 16">
    <path d="M3,7 L6,11 L13,4" fill="none" stroke="${color}" stroke-width="1"/>
  </svg>
`;
  return vscode.Uri.parse(
    "data:image/svg+xml;base64," + Buffer.from(svg).toString("base64")
  );
}

const verificationDecoration = vscode.window.createTextEditorDecorationType({
  gutterIconSize: "contain",
  light: {
    gutterIconPath: makeCheck("#6e6e6e"),
  },
  dark: {
    gutterIconPath: makeCheck("#858585"),
  },
});

// Should be used as a singleton.
class ProgressTracker {
  // The time we started expecting a build.
  // Also acts as a flag for whether we are tracking.
  startTime: number | null;

  // The id for the build that we are currently displaying in the UI.
  buildId: number | null;

  // Progress verifying each document.
  docs: { [url: string]: DocumentProgress };

  constructor() {
    this.startTime = null;
    this.buildId = null;
    this.docs = {};

    vscode.window.onDidChangeVisibleTextEditors((editors) => {
      for (let editor of editors) {
        this.updateDecorations(editor);
      }
    });
  }

  // Updates decorations for a particular editor.
  updateDecorations(editor: vscode.TextEditor) {
    if (editor.document.languageId !== "acorn") {
      // Not an Acorn file
      return;
    }

    let doc = this.docs[editor.document.uri.toString()];
    if (doc === undefined) {
      // We don't have any information for this document.
      // Clear the decorations.
      editor.setDecorations(verificationDecoration, []);
      return;
    }

    if (doc.version !== editor.document.version) {
      // The document has changed since we last verified it.
      // Just leave the decorations how they are.
      return;
    }

    // Update the decorations to reflect the state of the language server.
    let decorations: vscode.DecorationOptions[] = [];
    for (let [first_line, _] of doc.verified) {
      let range = new vscode.Range(first_line, 0, first_line, 0);
      decorations.push({ range });
    }
    editor.setDecorations(verificationDecoration, decorations);
  }

  // Fetches the current build progress from the language server.
  // Updates decorations if we get information from a new build.
  async getProgress(previousBuildId): Promise<ProgressResponse> {
    let response = (await client.sendRequest(
      "acorn/progress",
      {}
    )) as ProgressResponse;

    // No new progress
    if (response.buildId === previousBuildId) {
      return response;
    }

    this.buildId = response.buildId;
    this.docs = response.docs;

    for (let editor of vscode.window.visibleTextEditors) {
      this.updateDecorations(editor);
    }

    return response;
  }

  // Call this function when we think there might be a build soon.
  // It polls the language server for build progress and updates the UI.
  // Calling it multiple times is fine; subsequent simultaneous calls just return.
  // Note that a single call to 'track' can persist across many builds.
  // It returns when there is no longer an active build.
  async track() {
    if (this.startTime !== null) {
      return;
    }
    this.startTime = Date.now();
    try {
      await this.trackHelper();
    } catch (e) {
      console.error("error in progress tracker:", e);
    }
    this.startTime = null;
  }

  // Helper for track.
  // 'track' just handles error handling and preventing double-running.
  // trackHelper handles the progress bar.
  // Doesn't finish until the active build completes.
  async trackHelper() {
    let initialBuildId = this.buildId;

    let response: ProgressResponse = await this.getProgress(initialBuildId);

    while (response.buildId === initialBuildId) {
      // Maybe the next build just hasn't started yet.
      // Let's wait a bit and try again.
      await new Promise((resolve) => setTimeout(resolve, 100));
      response = await this.getProgress(initialBuildId);

      let elapsed = Date.now() - this.startTime;
      if (elapsed > 2000) {
        // It's been a while. Let's give up.
        console.log("giving up on progress bar");
        return;
      }
    }

    let previousPercent = 0;
    await vscode.window.withProgress(
      {
        location: vscode.ProgressLocation.Notification,
        title: "Acorn Verification",
        cancellable: true,
      },
      async (progress, token) => {
        token.onCancellationRequested(() => {
          console.log("acorn verification progress bar canceled");
        });

        while (!response.finished) {
          if (response.total > 0) {
            let percent = Math.floor((100 * response.done) / response.total);
            let increment = percent - previousPercent;
            progress.report({ increment });
            previousPercent = percent;
          }

          // Wait a bit before updating.
          await new Promise((resolve) => setTimeout(resolve, 100));
          response = await this.getProgress(null);
        }
      }
    );
  }
}

let tracker = new ProgressTracker();

// Figures out where the server executable is.
// Downloads it if necessary.
async function getServerPath(
  context: vscode.ExtensionContext
): Promise<string> {
  let extension = vscode.extensions.getExtension(context.extension.id);
  let timestamp = new Date().toLocaleTimeString();
  let version = extension.packageJSON.version;
  let binName = `acorn-${version}-${os.platform()}-${os.arch()}`;
  if (os.platform() === "win32") {
    binName += ".exe";
  }
  console.log(`activating ${binName} at`, timestamp);

  if (process.env.SERVER_PATH) {
    // Set explicitly in dev mode
    return process.env.SERVER_PATH;
  }

  // In production, the extension downloads a binary for the language server.
  let binDir = vscode.Uri.joinPath(context.globalStorageUri, "bin").fsPath;
  if (!fs.existsSync(binDir)) {
    fs.mkdirSync(binDir, { recursive: true });
    log(`created binary storage directory at ${binDir}`);
  }

  // Join the storage directory with the binary name
  let serverPath = path.join(binDir, binName);
  if (fs.existsSync(serverPath)) {
    // We already downloaded it
    return serverPath;
  }

  // Download the new binary from GitHub
  let oldBins = await fs.promises.readdir(binDir);
  let url = `https://github.com/acornprover/acorn/releases/download/v${version}/${binName}`;
  log(`downloading from ${url} to ${serverPath}`);
  await vscode.window.withProgress(
    {
      location: vscode.ProgressLocation.Notification,
      title: `Downloading ${binName} from GitHub...`,
      cancellable: false,
    },
    async () => {
      try {
        await downloadFile(url, serverPath);
      } catch (e) {
        // Pop up an error message
        vscode.window.showErrorMessage(
          `failed to download Acorn language server: ${e.message}`
        );
        log(`error downloading {url}: {e.message}`);
        throw e;
      }
    }
  );
  // Make the binary executable
  if (os.platform() !== "win32") {
    await fs.promises.chmod(serverPath, 0o755);
  }
  log("download complete");

  // Remove old binaries
  for (let oldBin of oldBins) {
    if (oldBin === binName) {
      // This shouldn't happen
      throw new Error("unexpected redownload");
    }
    let oldBinPath = path.join(binDir, oldBin);
    log(`removing old binary ${oldBinPath}`);
    fs.unlinkSync(oldBinPath);
  }

  return serverPath;
}

async function registerCommands(context: vscode.ExtensionContext) {
  // Create a new Acorn file
  let newFile = vscode.commands.registerCommand(
    "acornprover.newFile",
    async () => {
      let document = await vscode.workspace.openTextDocument({
        language: "acorn",
      });
      await vscode.window.showTextDocument(document);
    }
  );
  context.subscriptions.push(newFile);

  // Clear the binary cache, to redownload the language server.
  let clearBinaryCache = vscode.commands.registerCommand(
    "acornprover.clearBinaryCache",
    async () => {
      let binDir = vscode.Uri.joinPath(context.globalStorageUri, "bin").fsPath;
      let oldBins = await fs.promises.readdir(binDir);
      for (let oldBin of oldBins) {
        let oldBinPath = path.join(binDir, oldBin);
        log(`removing ${oldBinPath}`);
        fs.unlinkSync(oldBinPath);
      }
      log("binary cache cleared");

      vscode.commands.executeCommand("workbench.action.reloadWindow");
    }
  );
  context.subscriptions.push(clearBinaryCache);

  // Show server logs
  let showServerLogs = vscode.commands.registerCommand(
    "acornprover.showServerLogs",
    () => {
      client.outputChannel.show(true);
    }
  );
  context.subscriptions.push(showServerLogs);
}

export async function activate(context: vscode.ExtensionContext) {
  let command = await getServerPath(context);

  // Build the serve subcommand arguments
  let acornlibCacheDir = vscode.Uri.joinPath(
    context.globalStorageUri,
    "acornlib"
  ).fsPath;
  let args = ["serve", "--acornlib-cache-dir", acornlibCacheDir];
  if (
    vscode.workspace.workspaceFolders &&
    vscode.workspace.workspaceFolders.length > 0
  ) {
    let workspaceRoot = vscode.workspace.workspaceFolders[0].uri.fsPath;
    args.push("--workspace-root", workspaceRoot);
  }

  let exec: Executable = {
    command,
    args,
    options: {
      env: {
        RUST_BACKTRACE: "1",
        ...process.env,
      },
    },
  };

  // Currently we don't do anything differently in debug mode.
  let serverOptions: ServerOptions = {
    run: exec,
    debug: exec,
  };

  let initFailed = false;

  let clientOptions: LanguageClientOptions = {
    // Register the server for Acorn documents
    documentSelector: [
      { scheme: "file", language: "acorn" },
      { scheme: "untitled", language: "acorn" },
    ],
    synchronize: {
      // Notify the server about file changes to '.clientrc files contained in the workspace
      fileEvents: vscode.workspace.createFileSystemWatcher("**/.clientrc"),
    },
    initializationFailedHandler: (error) => {
      initFailed = true;
      let message = error.message;
      let manifestMessageStart = message.indexOf(
        "This version of acornlib uses project format "
      );
      if (manifestMessageStart >= 0) {
        message = message.slice(manifestMessageStart);
      } else {
        message = "Acorn error: " + message;
      }
      vscode.window.showErrorMessage(message);
      // Prevent automatic restart
      return false;
    },
    errorHandler: {
      error: (error, message, count) => {
        console.error("Language server error:", error);
        // Do not restart on error
        return { action: ErrorAction.Shutdown, handled: initFailed };
      },
      closed: () => {
        console.warn("Language server process closed.");

        // Show error message with option to view logs
        vscode.window
          .showErrorMessage(
            "The Acorn language server crashed. Please report this bug to the developer!",
            "View Logs"
          )
          .then((selection) => {
            if (selection === "View Logs") {
              client.outputChannel.show(true);
            }
          });

        // Do not restart on process close
        return { action: CloseAction.DoNotRestart, handled: initFailed };
      },
    },
  };

  // Create the language client and start the client.
  client = new LanguageClient(
    "acornLanguageServer",
    "Acorn Language Server",
    serverOptions,
    clientOptions
  );

  // Start the client. This will also launch the server
  try {
    await client.start();
  } catch (e) {
    console.error("client failed to start:", e);
    return;
  }

  let assistantPath = context.asAbsolutePath("build/assistant");
  let assistant = new Assistant(client, assistantPath);
  context.subscriptions.push(assistant);

  for (let doc of vscode.workspace.textDocuments) {
    if (doc.languageId === "acorn") {
      // Track the initial build.
      // No await, because we don't want to block the UI thread.
      tracker.track();
      break;
    }
  }

  await registerCommands(context);

  assistant.maybeShow();

  let onSaveOrOpen = async (document: vscode.TextDocument) => {
    if (document.languageId !== "acorn") {
      return;
    }
    await tracker.track();
  };

  context.subscriptions.push(
    vscode.workspace.onDidSaveTextDocument(onSaveOrOpen)
  );
  context.subscriptions.push(
    vscode.workspace.onDidOpenTextDocument(onSaveOrOpen)
  );
  context.subscriptions.push(
    vscode.window.onDidChangeActiveTextEditor(() => {
      assistant.maybeShow();
    })
  );
}

export function deactivate(): Thenable<void> | undefined {
  if (!client || !client.isRunning()) {
    return undefined;
  }
  return client.stop();
}
