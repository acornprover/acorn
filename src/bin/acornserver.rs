// The Acorn Language Server. This is typically invoked by a VS Code extension.

use std::collections::HashMap;
use std::path::PathBuf;
use std::sync::atomic::AtomicBool;
use std::sync::Arc;

use acorn::live_document::LiveDocument;
use chrono;
use clap::Parser;
use dashmap::DashMap;
use tokio::sync::{mpsc, Mutex, RwLock, RwLockWriteGuard};
use tower_lsp::jsonrpc;
use tower_lsp::lsp_types::*;
use tower_lsp::{Client, LanguageServer, LspService, Server};

use acorn::block::NodeCursor;
use acorn::builder::Builder;
use acorn::interfaces::{
    InfoParams, InfoResponse, ProgressParams, ProgressResponse, SearchParams, SearchResponse,
    SearchStatus,
};
use acorn::module::{Module, ModuleRef};
use acorn::project::Project;
use acorn::prover::{Outcome, Prover};

#[derive(Parser)]
struct Args {
    // The root folder the user has open
    #[clap(long)]
    workspace_root: Option<String>,

    // The root folder of the extension
    #[clap(long)]
    extension_root: String,
}

// These messages will show up in the "Acorn Language Server" channel in the output tab.
// User-visible, if the user looks for them.
fn log(message: &str) {
    let timestamp = chrono::Local::now().format("%H:%M:%S%.3f");
    let stamped = format!("[{}] {}", timestamp, message);
    eprintln!("{}", stamped);
}

fn log_with_doc(url: &Url, version: i32, message: &str) {
    // Extract the last component of the url
    let filename = url.path_segments().unwrap().last().unwrap();
    let versioned = format!("{} v{}: {}", filename, version, message);
    log(&versioned);
}

// A search task is a long-running task that searches for a proof.
// The language server can work on one search task at a time.
// The SearchTask tracks information around that request.
// It is clonable so that it can be used both by the thread doing the task, and
// threads handling requests.
// The thread doing the search updates the task with its information, while threads handling
// concurrent user requests can read it.
#[derive(Clone)]
struct SearchTask {
    project: Arc<RwLock<Project>>,
    url: Url,
    version: i32,

    // While we are proving, most of the time the thread running the 'run' method
    // will hold a write lock on the prover.
    // The task will release and reacquire the lock intermittently, and the RwLock is fair so other
    // threads get a chance to use the prover.
    prover: Arc<RwLock<Prover>>,

    // The module that we're searching for a proof in
    module_ref: ModuleRef,

    // The line in the document the user selected to kick off this task.
    selected_line: u32,

    // The path to the goal
    path: Vec<usize>,

    // A displayable name for the goal
    goal_name: String,

    // The range of the goal in the document
    goal_range: Range,

    // The Status is periodically updated by the task.
    // It can indicate either partial progress or completion.
    status: Arc<RwLock<SearchStatus>>,

    // Set this flag to true when a subsequent search task has been created
    superseded: Arc<AtomicBool>,

    // Zero-based line where we would insert a proof for this goal
    proof_insertion_line: u32,

    // Whether we need to also insert a block, if we do insert a proof.
    insert_block: bool,

    // The search id set by the extenson for the original search that created this task.
    // The extension may send new searches with essentially the same parameters, that we
    // discard. This is inevitable because the extension doesn't have enough information to
    // disambiguate searches. Only the language server does.
    // Thus, when we get redundant searches, we keep using the original id downstream.
    id: i32,
}

impl SearchTask {
    // Makes a response based on the current state of the task
    async fn response(&self) -> SearchResponse {
        let status = self.status.read().await.clone();
        SearchResponse {
            uri: self.url.clone(),
            version: self.version,
            failure: None,
            loading: false,
            goal_name: Some(self.goal_name.clone()),
            goal_range: Some(self.goal_range.clone()),
            status,
            proof_insertion_line: self.proof_insertion_line,
            insert_block: self.insert_block,
            id: self.id,
        }
    }

    // Runs the search task.
    async fn run(&self) {
        // This holds a read lock on the project the whole time.
        // It seems like we should be able to avoid this, but maybe it's just fine.
        let project = self.project.read().await;
        let env = match project.get_env_by_ref(&self.module_ref) {
            Some(env) => env,
            None => {
                log(&format!("no environment for {:?}", self.module_ref));
                return;
            }
        };

        log(&format!("running search task for {}", self.goal_name));

        loop {
            // Each iteration through the loop reacquires the write lock on the prover.
            // This lets other threads access the prover in between iterations.
            let mut prover = self.prover.write().await;
            let outcome = prover.partial_search();
            let status = match outcome {
                Outcome::Success => {
                    let proof = prover.get_proof().unwrap();
                    let steps = prover.to_proof_info(&project, &env.bindings, &proof);

                    let (code, error) = match proof.to_code(&env.bindings) {
                        Ok(code) => (Some(code), None),
                        Err(e) => (None, Some(e.to_string())),
                    };

                    SearchStatus::success(code, error, steps, proof.needs_simplification(), &prover)
                }

                Outcome::Inconsistent
                | Outcome::Exhausted
                | Outcome::Constrained
                | Outcome::Error => SearchStatus::stopped(&prover, outcome),

                Outcome::Timeout => SearchStatus::pending(&prover),

                Outcome::Interrupted => {
                    // No point in providing a result for this task, since nobody is listening.
                    log(&format!("goal {} interrupted", self.goal_name));
                    return;
                }
            };

            // Update the status
            let mut locked_status = self.status.write().await;
            *locked_status = status;

            if outcome != Outcome::Timeout {
                // We're done
                log(&format!("search task for {} completed", self.goal_name));
                break;
            }
        }
    }
}

// One Backend per root folder.
// The Backend implements a similar API to the LanguageServer API, but it doesn't implement
// "initialize" because that's used by the LazyBackend to create the Backend.
struct Backend {
    client: Client,

    // The project we're working on
    project: Arc<RwLock<Project>>,

    // Progress requests share this value with the client.
    // Search tasks update it as they go.
    progress: Arc<Mutex<ProgressResponse>>,

    // Maps uri to its document. The LiveDocument tracks changes.
    documents: DashMap<Url, Arc<RwLock<LiveDocument>>>,

    // The current search task, if any
    search_task: Arc<RwLock<Option<SearchTask>>>,

    // All the diagnostics that are currently published for the project.
    diagnostic_map: Arc<RwLock<HashMap<Url, Vec<Diagnostic>>>>,
}

// Finds the acorn library to use, given the root folder for the current workspace.
// Falls back to the library bundled with the extension.
// Panics if we can't find either.
fn find_acorn_library(args: &Args) -> PathBuf {
    // Check for a local library, near the code
    if let Some(workspace_root) = &args.workspace_root {
        let path = PathBuf::from(&workspace_root);
        if let Some(library_root) = Project::find_local_acorn_library(&path) {
            return library_root;
        }
    }

    // Use the bundled library.
    let library_root = PathBuf::from(&args.extension_root).join("acornlib");
    if !library_root.exists() {
        panic!(
            "packaging error: no acorn library at {}",
            library_root.display()
        );
    }
    library_root
}

impl Backend {
    // Creates a new backend.
    // Determines which library to use based on the root of the current workspace.
    // If we can't find one in a logical location based on the editor, we use
    // the library bundled with the extension.
    fn new(client: Client) -> Backend {
        let args = Args::parse();
        let library_root = find_acorn_library(&args);

        log(&format!(
            "using acorn library at {}",
            library_root.display()
        ));

        let project = Project::new(library_root);
        Backend {
            project: Arc::new(RwLock::new(project)),
            client,
            progress: Arc::new(Mutex::new(ProgressResponse::default())),
            documents: DashMap::new(),
            search_task: Arc::new(RwLock::new(None)),
            diagnostic_map: Arc::new(RwLock::new(HashMap::new())),
        }
    }

    // Run a build in a background thread, proving the goals in all open documents.
    // Both spawned threads hold a read lock on the project while doing their work.
    // This ensures that the project doesn't change for the duration of the build.
    fn spawn_build(&self) {
        let start_time = chrono::Local::now();

        // This channel passes the build events
        let (tx, mut rx) = mpsc::unbounded_channel();

        // Spawn a thread to run the build.

        let project = self.project.clone();
        tokio::spawn(async move {
            let project = project.read().await;

            tokio::task::block_in_place(move || {
                let mut builder = Builder::new(move |event| {
                    tx.send(event).unwrap();
                });
                project.build(&mut builder);

                let duration = chrono::Local::now() - start_time;
                let seconds = duration.num_milliseconds() as f64 / 1000.0;
                log(&format!(
                    "verification {} after {:.2}s",
                    builder.status.verb(),
                    seconds
                ));
            });
        });

        // Spawn a thread to process the build events.
        let project = self.project.clone();
        let progress = self.progress.clone();
        let client = self.client.clone();
        let diagnostic_map = self.diagnostic_map.clone();
        tokio::spawn(async move {
            // Clear any diagnostics from the previous build
            let mut diagnostic_map = diagnostic_map.write().await;
            for url in diagnostic_map.keys() {
                client.publish_diagnostics(url.clone(), vec![], None).await;
            }
            diagnostic_map.clear();

            let project = project.read().await;
            while let Some(event) = rx.recv().await {
                if let Some((done, total)) = event.progress {
                    if total > 0 {
                        let mut locked_progress = progress.lock().await;
                        *locked_progress = ProgressResponse { done, total };
                    }
                }

                if let Some(message) = event.log_message {
                    log(&message);
                }

                if let Some((module_ref, diagnostic)) = event.diagnostic {
                    let path = match project.path_from_module_ref(&module_ref) {
                        Some(path) => path,
                        None => {
                            log(&format!(
                                "cannot publish diagnostic; no path available for {:?}",
                                module_ref
                            ));
                            return;
                        }
                    };
                    let url = Url::from_file_path(path).unwrap();
                    let diagnostics = diagnostic_map.entry(url.clone()).or_default();
                    if let Some(d) = diagnostic {
                        diagnostics.push(d);
                    }
                    client
                        .publish_diagnostics(url, diagnostics.clone(), None)
                        .await;
                }
            }
        });
    }

    // Update the full text of the document.
    // For an open, we get the document version.
    // For a save, we don't, but we can find the version, because the version we're saving is the same
    // as the version of the last change we received.
    // After this call both the live version and the saved version should be the same.
    async fn set_full_text(&self, url: Url, text: String, version: Option<i32>) {
        // Update the live document in the document map
        let version = match version {
            Some(version) => {
                // This is an "open".
                // This document might have been open before. Just create a new one.
                log_with_doc(&url, version, "new document");
                let doc = LiveDocument::new(&text, version);
                self.documents
                    .insert(url.clone(), Arc::new(RwLock::new(doc)));
                version
            }
            None => {
                // This is a "save".
                // We should have a document already, so mutate it.
                let doc = match self.documents.get(&url) {
                    Some(doc) => doc,
                    None => {
                        log(&format!("no document available for {}", url));
                        return;
                    }
                };
                let mut doc = doc.write().await;
                doc.save(&text)
            }
        };

        let path = match url.to_file_path() {
            Ok(path) => path,
            Err(_) => {
                log(&format!("cannot update doc; no path available for {}", url));
                return;
            }
        };

        {
            // Check if the project already has this document state.
            // If the update is a no-op, there's no need to stop the build.
            // This can happen if we are opening a document that the project is already using.
            let project = self.project.read().await;
            if project.has_version(&path, version) {
                return;
            }
        }

        let mut project = self.stop_build_and_get_project().await;
        log(&format!(
            "updating {} with {} bytes",
            path.display(),
            text.len()
        ));
        match project.update_file(path, &text, version) {
            Ok(()) => {}
            Err(e) => log(&format!("update failed: {:?}", e)),
        }
        self.spawn_build();
    }

    // If there is a build happening, stops it.
    // Acquires the write lock on the project.
    // Returns a writable reference to the project.
    async fn stop_build_and_get_project(&self) -> RwLockWriteGuard<Project> {
        {
            let project = self.project.read().await;
            project.stop_build();
        }
        // Reallow the build once we acquire the write lock
        let mut project = self.project.write().await;
        project.allow_build();
        project
    }

    fn search_fail(&self, params: SearchParams, message: &str) -> jsonrpc::Result<SearchResponse> {
        log(message);
        Ok(SearchResponse {
            failure: Some(message.to_string()),
            ..SearchResponse::new(params)
        })
    }

    async fn handle_progress_request(
        &self,
        _params: ProgressParams,
    ) -> jsonrpc::Result<ProgressResponse> {
        let locked_progress = self.progress.lock().await;
        Ok(locked_progress.clone())
    }

    // Cancels any current search task.
    // Runs the new task, if it is not None.
    async fn set_search_task(&self, new_task: Option<SearchTask>) {
        // Replace the locked singleton task
        {
            let mut locked_task = self.search_task.write().await;
            if let Some(old_task) = locked_task.as_ref() {
                // Cancel the old task
                old_task
                    .superseded
                    .store(true, std::sync::atomic::Ordering::Relaxed);
            }
            *locked_task = new_task.clone();
        }

        if let Some(new_task) = new_task {
            tokio::spawn(async move {
                new_task.run().await;
            });
        }
    }

    async fn handle_search_request(&self, params: SearchParams) -> jsonrpc::Result<SearchResponse> {
        let doc = match self.documents.get(&params.uri) {
            Some(doc) => doc,
            None => {
                return self.search_fail(params, "no text available");
            }
        };
        let doc = doc.read().await;

        // Check if this request matches our current task, based on the selected line.
        // This is less general than checking the full path, but we don't have the
        // full path until we acquire a lock on the project.
        if let Some(current_task) = self.search_task.read().await.as_ref() {
            if current_task.url == params.uri
                && current_task.version == params.version
                && current_task.selected_line == params.selected_line
            {
                return Ok(current_task.response().await);
            }
        }

        let project = self.project.read().await;
        let path = match params.uri.to_file_path() {
            Ok(path) => path,
            Err(_) => {
                // There should be a path available, because we don't run this task without one.
                return self.search_fail(params, "no path available in SearchTask::run");
            }
        };
        match project.get_version(&path) {
            Some(project_version) => {
                if params.version < project_version {
                    let message = &format!(
                        "user requested version {} but the project has version {}",
                        params.version, project_version
                    );
                    return self.search_fail(params, message);
                }
                if params.version > project_version {
                    // The requested version is not loaded yet.
                    return Ok(SearchResponse {
                        loading: true,
                        ..SearchResponse::new(params)
                    });
                }
            }
            None => {
                return self.search_fail(
                    params,
                    &format!("the project has not opened {}", path.display()),
                );
            }
        }
        let module_ref = match project.module_ref_from_path(&path) {
            Ok(name) => name,
            Err(e) => {
                return self.search_fail(params, &format!("module_ref_from_path failed: {:?}", e))
            }
        };
        let env = match project.get_module_by_ref(&module_ref) {
            Module::Ok(env) => env,
            _ => {
                return self.search_fail(
                    params,
                    &format!("could not load module from {:?}", module_ref),
                );
            }
        };

        let path = match env.path_for_line(params.selected_line) {
            Ok(path) => path,
            Err(s) => return self.search_fail(params, &s),
        };

        // Check if this request matches our current task, based on the full path of the goal.
        // This is slower (because we had to acquire the project lock first)
        // but catches more situations than just checking the selected line.
        if let Some(current_task) = self.search_task.read().await.as_ref() {
            if current_task.url == params.uri
                && current_task.version == params.version
                && current_task.path == path
            {
                return Ok(current_task.response().await);
            }
        }
        let node = NodeCursor::from_path(env, &path);
        let goal_context = match node.goal_context() {
            Ok(goal_context) => goal_context,
            Err(s) => return self.search_fail(params, &s),
        };
        let superseded = Arc::new(AtomicBool::new(false));
        let mut prover = Prover::new(&project, false);
        for fact in node.usable_facts(&project) {
            prover.add_fact(fact);
        }
        prover.set_goal(&goal_context);
        prover.stop_flags.push(superseded.clone());
        let status = SearchStatus::pending(&prover);

        // Create a new search task
        let new_task = SearchTask {
            project: self.project.clone(),
            url: params.uri.clone(),
            version: doc.saved_version(),
            prover: Arc::new(RwLock::new(prover)),
            module_ref,
            selected_line: params.selected_line,
            path,
            goal_name: goal_context.name.clone(),
            goal_range: goal_context.goal.range(),
            status: Arc::new(RwLock::new(status)),
            superseded,
            proof_insertion_line: goal_context.proof_insertion_line,
            insert_block: goal_context.insert_block,
            id: params.id,
        };

        // A minimal response before any data has been collected
        let mut response = new_task.response().await;
        response.loading = true;

        self.set_search_task(Some(new_task)).await;

        Ok(response)
    }

    fn info_fail(&self, params: InfoParams, message: &str) -> jsonrpc::Result<InfoResponse> {
        log(message);
        Ok(InfoResponse {
            search_id: params.search_id,
            failure: Some(message.to_string()),
            result: None,
        })
    }

    async fn handle_info_request(&self, params: InfoParams) -> jsonrpc::Result<InfoResponse> {
        let locked_task = self.search_task.read().await;

        let task = match locked_task.as_ref() {
            Some(task) => task,
            None => return self.info_fail(params, "no search task available"),
        };
        if task.id != params.search_id {
            let failure = format!(
                "info request has search id {}, task has id {}",
                params.search_id, task.id
            );
            return self.info_fail(params, &failure);
        }
        let project = self.project.read().await;
        let prover = task.prover.read().await;
        let env = match project.get_env_by_ref(&task.module_ref) {
            Some(env) => env,
            None => {
                return self.info_fail(params, "no environment available");
            }
        };
        let result = prover.info_result(&project, &env.bindings, params.clause_id);
        let failure = match result {
            Some(_) => None,
            None => Some(format!("no info available for clause {}", params.clause_id)),
        };
        Ok(InfoResponse {
            search_id: params.search_id,
            failure,
            result,
        })
    }
}

#[tower_lsp::async_trait]
impl LanguageServer for Backend {
    async fn initialize(&self, _params: InitializeParams) -> jsonrpc::Result<InitializeResult> {
        let sync_options = TextDocumentSyncCapability::Options(TextDocumentSyncOptions {
            open_close: Some(true),
            change: Some(TextDocumentSyncKind::INCREMENTAL),
            save: Some(TextDocumentSyncSaveOptions::SaveOptions(SaveOptions {
                include_text: Some(true),
            })),
            ..TextDocumentSyncOptions::default()
        });

        Ok(InitializeResult {
            server_info: None,
            capabilities: ServerCapabilities {
                text_document_sync: Some(sync_options),
                completion_provider: Some(CompletionOptions::default()),
                ..ServerCapabilities::default()
            },
        })
    }

    async fn did_save(&self, params: DidSaveTextDocumentParams) {
        let uri = params.text_document.uri;
        let text = match params.text {
            Some(text) => text,
            None => {
                log("no text available in did_save");
                return;
            }
        };
        self.set_full_text(uri, text, None).await;
    }

    async fn did_open(&self, params: DidOpenTextDocumentParams) {
        let url = params.text_document.uri;
        let text = params.text_document.text;
        let version = params.text_document.version;
        self.set_full_text(url, text, Some(version)).await;
    }

    // Just updates the current version, doesn't rebuild anything
    async fn did_change(&self, params: DidChangeTextDocumentParams) {
        let url = params.text_document.uri;
        let version = params.text_document.version;
        if let Some(doc) = self.documents.get(&url) {
            let mut doc = doc.write().await;
            for change in params.content_changes {
                if let Err(e) = doc.change(change.range, &change.text, version) {
                    log(&format!("change failed: {}", e));
                }
            }
        }
    }

    async fn did_close(&self, params: DidCloseTextDocumentParams) {
        let uri = params.text_document.uri;
        if let Some(old_doc) = self.documents.get(&uri) {
            log_with_doc(&uri, old_doc.read().await.saved_version(), "closed");
        }
        self.documents.remove(&uri);
        let mut project = self.stop_build_and_get_project().await;
        match project.close_file(uri.to_file_path().unwrap()) {
            Ok(()) => {}
            Err(e) => log(&format!("close failed: {:?}", e)),
        }
    }

    async fn completion(
        &self,
        _params: CompletionParams,
    ) -> jsonrpc::Result<Option<CompletionResponse>> {
        // Return None, indicating no completions
        log("XXX completion");
        Ok(None)
    }

    async fn shutdown(&self) -> jsonrpc::Result<()> {
        log("shutdown");
        Ok(())
    }
}

#[tokio::main]
async fn main() {
    let stdin = tokio::io::stdin();
    let stdout = tokio::io::stdout();

    let (service, socket) = LspService::build(Backend::new)
        .custom_method("acorn/info", Backend::handle_info_request)
        .custom_method("acorn/progress", Backend::handle_progress_request)
        .custom_method("acorn/search", Backend::handle_search_request)
        .finish();

    Server::new(stdin, stdout, socket).serve(service).await;
}
