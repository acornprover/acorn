// The Acorn Language Server. This is typically invoked by a VS Code extension.
mod live_document;
mod project_manager;

use std::collections::HashMap;
use std::path::PathBuf;
use std::sync::Arc;

use self::live_document::LiveDocument;
use self::project_manager::ProjectManager;
use crate::builder::{BuildEvent, Builder};
use color_backtrace::BacktracePrinter;
use dashmap::DashMap;
use tokio::sync::{mpsc, RwLock};
use tower_lsp::jsonrpc;
use tower_lsp::lsp_types::request::GotoImplementationResponse;
use tower_lsp::lsp_types::*;
use tower_lsp::{Client, LanguageServer, LspService, Server};

use crate::interfaces::{
    DocumentProgress, ProgressParams, ProgressResponse, SelectionParams, SelectionResponse,
};
use crate::project::{Project, ProjectConfig, SelectionInfo};

// Trait abstracting the LSP client methods we need
#[async_trait::async_trait]
pub trait LspClient: Send + Sync {
    async fn publish_diagnostics(
        &self,
        uri: Url,
        diagnostics: Vec<Diagnostic>,
        version: Option<i32>,
    );
}

// Implement LspClient for tower_lsp::Client
#[async_trait::async_trait]
impl LspClient for Client {
    async fn publish_diagnostics(
        &self,
        uri: Url,
        diagnostics: Vec<Diagnostic>,
        version: Option<i32>,
    ) {
        self.publish_diagnostics(uri, diagnostics, version).await;
    }
}

pub struct ServerArgs {
    // The root folder the user has open
    pub workspace_root: Option<String>,

    // The root folder of the extension
    pub extension_root: String,
}

// These messages will show up in the "Acorn Language Server" channel in the output tab.
// User-visible, if the user looks for them.
fn log(message: &str) {
    let timestamp = chrono::Local::now().format("%H:%M:%S%.3f");
    let stamped = format!("[{}] {}", timestamp, message);
    eprintln!("{}", stamped);
}

// Only converts to path if it's a file scheme.
// The Rust docs claim that the regular to_file_path shouldn't be relied on for this.
fn to_path(url: &Url) -> Option<PathBuf> {
    if url.scheme() == "file" {
        url.to_file_path().ok()
    } else {
        None
    }
}

fn log_with_url(url: &Url, version: i32, message: &str) {
    let versioned = format!("{} v{}: {}", url, version, message);
    log(&versioned);
}

// The part of the Build that is relevant to a single document.
struct DocumentBuildInfo {
    // The version of the document that we built with.
    // If we got it from the filesystem, there is no version.
    version: Option<i32>,

    // The line ranges with goals that have been verified.
    // Should not include any ranges that are subsumed, or overlap with diagnostics.
    verified: Vec<(u32, u32)>,

    // Errors and warnings that have been generated for this document.
    diagnostics: Vec<Diagnostic>,
}

impl DocumentBuildInfo {
    fn new(version: Option<i32>) -> DocumentBuildInfo {
        DocumentBuildInfo {
            version,
            verified: vec![],
            diagnostics: vec![],
        }
    }

    // Called when a new goal has been verified.
    fn verify(&mut self, first_line: u32, last_line: u32) {
        if let Some(diagnostic) = self.diagnostics.last() {
            // If the last diagnostic overlaps with this goal, that means we can verify
            // the final step of the proof, but not all the previous steps.
            // In this case, we don't report the verification downstream.
            if diagnostic.range.end.line >= first_line && diagnostic.range.start.line <= last_line {
                return;
            }
        }

        // We can clear any previous verifications that are subsumed by this one.
        while let Some((line, _)) = self.verified.last() {
            if *line < first_line {
                break;
            }
            self.verified.pop();
        }
        self.verified.push((first_line, last_line));
    }

    // Called when a new problem has been reported.
    fn add_diagnostic(&mut self, diagnostic: Diagnostic) {
        self.diagnostics.push(diagnostic);
    }
}

// Information about the most recent build.
struct BuildInfo {
    // An id for the build, unique per run of the language server.
    // If this is None, we do not intend to be showing information for any build.
    id: Option<u32>,

    // How many goals have been verified.
    done: i32,
    total: i32,

    // Whether the build is finished or not.
    // Distinguishes the scenarios:
    //   1. This build is 0/0 complete because it finished its zero goals
    //   2. This build is 0/0 complete because it hasn't counted the goals yet
    finished: bool,

    // Per-document information
    docs: HashMap<Url, DocumentBuildInfo>,
}

impl BuildInfo {
    // A placeholder representing no build.
    fn none() -> BuildInfo {
        BuildInfo {
            id: None,
            done: 0,
            total: 0,
            finished: false,
            docs: HashMap::new(),
        }
    }

    // Turn the known build information into a progress response.
    fn progress(&self) -> ProgressResponse {
        let mut docs = HashMap::new();
        for (url, doc) in &self.docs {
            // No need to report verified lines for files that aren't open.
            if let Some(version) = doc.version {
                docs.insert(
                    url.clone(),
                    DocumentProgress {
                        version,
                        verified: doc.verified.clone(),
                    },
                );
            }
        }
        ProgressResponse {
            build_id: self.id,
            done: self.done,
            total: self.total,
            finished: self.finished,
            docs,
        }
    }

    fn finish(&mut self) {
        self.finished = true;
    }

    // Take a function that modifies a DocumentBuildInfo and apply it to the document.
    // Creates a new entry if the document is not already in the map.
    fn with_doc(
        &mut self,
        url: &Url,
        f: impl FnOnce(&mut DocumentBuildInfo),
    ) -> &DocumentBuildInfo {
        let doc = self
            .docs
            .entry(url.clone())
            .or_insert_with(|| DocumentBuildInfo::new(None));
        f(doc);
        doc
    }

    // Clears everything in preparation for a new build.
    // Then sets docs for the open documents.
    async fn reset(&mut self, project: &Project, client: &Arc<dyn LspClient>) {
        // Clear the diagnostics for all the open documents.
        let mut new_docs = HashMap::new();
        for (url, version) in project.open_urls() {
            client
                .publish_diagnostics(url.clone(), vec![], Some(version))
                .await;
            new_docs.insert(url, DocumentBuildInfo::new(Some(version)));
        }
        // Clear the diagnostics for any closed documents.
        for url in self.docs.keys() {
            if !new_docs.contains_key(url) {
                client.publish_diagnostics(url.clone(), vec![], None).await;
            }
        }
        *self = BuildInfo::none();
        self.docs = new_docs;
    }

    async fn handle_event(
        &mut self,
        project: &Project,
        client: &Arc<dyn LspClient>,
        event: &BuildEvent,
    ) {
        if Some(event.build_id) != self.id {
            if self.id.is_some() {
                log("warning: a new build started without clearing the old one");
                return;
            }
            self.id = Some(event.build_id);
        }
        if let Some((done, total)) = event.progress {
            self.done = done;
            self.total = total;
        }
        if let Some(message) = &event.log_message {
            log(message);
        }
        if let Some(url) = project.url_from_descriptor(&event.module) {
            if let Some((first_line, last_line)) = &event.verified {
                self.with_doc(&url, |doc| {
                    doc.verify(*first_line, *last_line);
                });
            }
            if let Some(diagnostic) = &event.diagnostic {
                let doc = self.with_doc(&url, |doc| {
                    doc.add_diagnostic(diagnostic.clone());
                });
                client
                    .publish_diagnostics(url, doc.diagnostics.clone(), doc.version)
                    .await;
            }
        }
    }
}

// VS Code will create separate language servers for each of its workspace folders.
pub struct AcornLanguageServer {
    client: Arc<dyn LspClient>,

    // The project we're working on
    project_manager: Arc<ProjectManager>,

    // Information about the most recent build to run.
    build: Arc<RwLock<BuildInfo>>,

    // Maps uri to its document. The LiveDocument tracks changes.
    pub documents: DashMap<Url, Arc<RwLock<LiveDocument>>>,
}

// Finds the acorn library to use, given the root folder for the current workspace.
// Falls back to the library bundled with the extension.
// Returns (src_dir, build_dir, cache_writable).
// Panics if we can't find either.
fn find_acorn_library(args: &ServerArgs) -> (PathBuf, PathBuf, bool) {
    // Check for a local library, near the code
    if let Some(workspace_root) = &args.workspace_root {
        let path = PathBuf::from(&workspace_root);
        if let Some((src_dir, build_dir)) = Project::find_local_acorn_library(&path) {
            return (src_dir, build_dir, true);
        }
    }

    // Use the bundled library.
    let path = PathBuf::from(&args.extension_root).join("acornlib");
    if !path.exists() {
        panic!("packaging error: no acorn library at {}", path.display());
    }
    if let Some((src_dir, build_dir)) = Project::find_local_acorn_library(&path) {
        (src_dir, build_dir, false)
    } else {
        panic!(
            "packaging error: find_local_acorn_library failed for {}",
            path.display()
        );
    }
}

impl AcornLanguageServer {
    // Creates a new backend.
    // Determines which library to use based on the root of the current workspace.
    // If we can't find one in a logical location based on the editor, we use
    // the library bundled with the extension.
    // Returns an error if the build cache manifest version is too new.
    pub fn new(
        client: Arc<dyn LspClient>,
        args: &ServerArgs,
    ) -> Result<AcornLanguageServer, String> {
        let (src_dir, build_dir, write_cache) = find_acorn_library(&args);

        log(&format!(
            "using acorn server version {}",
            env!("CARGO_PKG_VERSION")
        ));
        log(&format!("using acorn library at {}", src_dir.display()));

        // The cache is always readable, only sometimes writable.
        let config = ProjectConfig {
            write_cache,
            ..Default::default()
        };
        let project_manager =
            Arc::new(ProjectManager::new(src_dir, build_dir, config).map_err(|e| e.to_string())?);
        Ok(AcornLanguageServer {
            project_manager,
            client,
            build: Arc::new(RwLock::new(BuildInfo::none())),
            documents: DashMap::new(),
        })
    }

    // Updates the project, then runs a build in a background thread.
    // Both spawned threads hold a read lock on the project while doing their work.
    // This ensures that the project doesn't change for the duration of the build.
    async fn build(&self, path: PathBuf, text: &str, version: i32) {
        log("building...");

        // Use mutate to update the file with automatic build cancellation
        let result = self
            .project_manager
            .mutate(|project| {
                project.building = true;
                project.update_file(path, &text, version)
            })
            .await;

        match result {
            Ok(()) => {}
            Err(e) => log(&format!("update failed: {:?}", e)),
        }

        let start_time = chrono::Local::now();

        // This channel passes the build events
        let (tx, mut rx) = mpsc::unbounded_channel();

        // Spawn a thread to run the build.
        let project_manager = self.project_manager.clone();
        tokio::spawn(async move {
            let project = project_manager.read().await;
            let epoch = project.epoch;

            let build_cache = tokio::task::block_in_place(move || {
                let mut builder = Builder::new(&*project, project.cancel.clone(), move |event| {
                    tx.send(event).unwrap();
                });
                builder.check_hashes = true;
                builder.build();

                let duration = chrono::Local::now() - start_time;
                let seconds = duration.num_milliseconds() as f64 / 1000.0;
                log(&format!(
                    "verification {} after {:.2}s",
                    builder.status.verb(),
                    seconds
                ));

                let lines = builder.metrics.info_lines().join(". ");
                log(&lines);

                // Return the build cache if successful
                builder.into_build_cache()
            });

            // Update the build cache if the build was successful and epoch hasn't changed.
            // Always mark building as false when done.
            let result = project_manager
                .mutate_if_epoch(epoch, |project| {
                    if let Some(new_cache) = build_cache {
                        // Server always does full builds of all targets, not partial builds
                        project.update_build_cache(new_cache, false);
                    }
                    project.building = false;
                })
                .await;

            match result {
                Ok(()) => log("build cache updated"),
                Err(()) => log("build cache update skipped (project changed during build)"),
            }
        });

        // Spawn a thread to process the build events.
        let project_manager = self.project_manager.clone();
        let build = self.build.clone();
        let client = Arc::clone(&self.client);
        tokio::spawn(async move {
            let project = project_manager.read().await;
            build.write().await.reset(&*project, &client).await;

            while let Some(event) = rx.recv().await {
                build
                    .write()
                    .await
                    .handle_event(&*project, &client, &event)
                    .await;
            }

            build.write().await.finish();
        });
    }

    pub async fn handle_progress_request(
        &self,
        _params: ProgressParams,
    ) -> jsonrpc::Result<ProgressResponse> {
        let progress = self.build.read().await.progress();
        Ok(progress)
    }

    pub async fn handle_selection_request(
        &self,
        params: SelectionParams,
    ) -> jsonrpc::Result<SelectionResponse> {
        let mut response = SelectionResponse::new(params.clone());

        let project = self.project_manager.read().await;
        response.building = project.building;
        let path = match to_path(&params.uri) {
            Some(path) => path,
            None => {
                response.failure = Some("no path available".to_string());
                return Ok(response);
            }
        };

        // Check if the requested version is loaded
        match project.get_version(&path) {
            Some(project_version) => {
                if params.version < project_version {
                    let message = format!(
                        "unexpected: selection has version {}, project has version {}",
                        params.version, project_version
                    );
                    log(&message);
                    response.failure = Some(message);
                    return Ok(response);
                }
                if params.version > project_version {
                    // The requested version is not loaded yet.
                    // "Loading" is a bit of a misnomer. We get a bunch of these requests whenever
                    // the document is unsaved.
                    response.loading = true;
                    return Ok(response);
                }
            }
            None => {
                // We don't have any version of this file.
                // Probably this indicates a file that is open in VS Code but unchanged.
                // Just fall through.
            }
        }

        match project.handle_selection(&path, params.selected_line) {
            Ok(SelectionInfo::Goals {
                goal_infos,
                goal_range,
            }) => {
                log(&format!(
                    "selection: {} at line {}, version {}, found {} goal(s)",
                    path.file_name().unwrap().to_string_lossy(),
                    params.selected_line,
                    params.version,
                    goal_infos.len()
                ));
                response.goals = goal_infos;
                response.goal_range = goal_range;
            }
            Ok(SelectionInfo::Citation(citation)) => {
                log(&format!(
                    "selection: {} at line {}, version {}, citation",
                    path.file_name().unwrap().to_string_lossy(),
                    params.selected_line,
                    params.version,
                ));
                response.citation = Some(citation);
            }
            Err(e) => {
                // This happens a lot when you click somewhere that doesn't match a goal.
                // It's fine, but there's no real reason to log it.
                response.failure = Some(e);
                return Ok(response);
            }
        }

        Ok(response)
    }
}

#[tower_lsp::async_trait]
impl LanguageServer for AcornLanguageServer {
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
                hover_provider: Some(HoverProviderCapability::Simple(true)),
                definition_provider: Some(OneOf::Left(true)),
                ..ServerCapabilities::default()
            },
        })
    }

    /// When did_open is called, we get a version number and the whole text of the document.
    /// We don't trigger builds on a file open.
    async fn did_open(&self, params: DidOpenTextDocumentParams) {
        let url = params.text_document.uri;
        let text = params.text_document.text;
        let version = params.text_document.version;

        // Create a new live document
        log_with_url(&url, version, "opened");
        let doc = LiveDocument::new(&text, version);
        self.documents
            .insert(url.clone(), Arc::new(RwLock::new(doc)));
    }

    /// When did_change is called, we get a version number and the changes to the document.
    /// The changes are in a "change event" format, which we do apply to the document.
    /// Currently we don't actually use the text content of the change event, though, because
    /// we don't rebuild on change.
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

    /// When did_save is called, we get the full text of the document.
    /// We don't get a version number, which is annoying. We have to take the last version number
    /// of the document that we saw in a change event.
    /// We trigger a build if it seems like we should.
    async fn did_save(&self, params: DidSaveTextDocumentParams) {
        let url = params.text_document.uri;
        let text = match params.text {
            Some(text) => text,
            None => {
                log("no text available in did_save");
                return;
            }
        };

        // Update the live document's saved version
        let version = {
            let doc = match self.documents.get(&url) {
                Some(doc) => doc,
                None => {
                    log(&format!("no document available for {}", url));
                    return;
                }
            };
            let mut doc = doc.write().await;
            doc.save(&text)
        };

        let path = match to_path(&url) {
            Some(path) => path,
            None => {
                // We don't pass on untitled documents to the project.
                return;
            }
        };

        {
            // Check if the project already has this document state.
            // If the update is a no-op, there's no need to stop the build.
            // This happens if you save without changing anything.
            let project = self.project_manager.read().await;
            if project.has_version(&path, version) {
                return;
            }
        }

        self.build(path, &text, version).await;
    }

    async fn did_close(&self, params: DidCloseTextDocumentParams) {
        let uri = params.text_document.uri;
        if let Some(old_doc) = self.documents.get(&uri) {
            log_with_url(&uri, old_doc.read().await.saved_version(), "closed");
        }
        self.documents.remove(&uri);
        let path = match to_path(&uri) {
            Some(path) => path,
            None => {
                // Looks like we're closing an untitled document.
                return;
            }
        };
        // Use mutate to close the file with automatic build cancellation
        let result = self
            .project_manager
            .mutate(|project| project.close_file(path))
            .await;

        match result {
            Ok(()) => {}
            Err(e) => log(&format!("close failed: {:?}", e)),
        }
    }

    async fn completion(
        &self,
        params: CompletionParams,
    ) -> jsonrpc::Result<Option<CompletionResponse>> {
        let uri = params.text_document_position.text_document.uri;
        let path = to_path(&uri);
        let pos = params.text_document_position.position;
        let doc = match self.documents.get(&uri) {
            Some(doc) => doc,
            None => {
                log("no document available for completion");
                return Ok(None);
            }
        };
        let doc = doc.read().await;
        let env_line = doc.get_env_line(pos.line);
        let prefix = doc.get_prefix(pos.line, pos.character);
        let project = self.project_manager.read().await;
        match project.get_completions(path.as_deref(), env_line, &prefix) {
            Some(items) => {
                let response = CompletionResponse::List(CompletionList {
                    is_incomplete: false,
                    items,
                });
                Ok(Some(response))
            }
            None => Ok(None),
        }
    }

    async fn hover(&self, params: HoverParams) -> jsonrpc::Result<Option<Hover>> {
        let uri = params.text_document_position_params.text_document.uri;
        let pos = params.text_document_position_params.position;
        let project = self.project_manager.read().await;

        // We log something in the conditions that are unexpected
        let Some(path) = to_path(&uri) else {
            log(&format!("could not convert to path: {}", uri));
            return Ok(None);
        };
        let Ok(descriptor) = project.descriptor_from_path(&path) else {
            log(&format!(
                "could not get descriptor for path: {}",
                path.display()
            ));
            return Ok(None);
        };
        let Some(env) = project.get_env(&descriptor) else {
            log(&format!(
                "no environment for module: {:?} (try saving?)",
                descriptor
            ));
            return Ok(None);
        };

        Ok(project.hover(&env, pos.line, pos.character))
    }

    async fn shutdown(&self) -> jsonrpc::Result<()> {
        log("shutdown");
        Ok(())
    }

    async fn goto_definition(
        &self,
        params: GotoDefinitionParams,
    ) -> jsonrpc::Result<Option<GotoImplementationResponse>> {
        let uri = params.text_document_position_params.text_document.uri;
        let pos = params.text_document_position_params.position;
        let project = self.project_manager.read().await;

        // We log something in the conditions that are unexpected
        let Some(path) = to_path(&uri) else {
            log(&format!("could not convert to path: {}", uri));
            return Ok(None);
        };
        let Ok(descriptor) = project.descriptor_from_path(&path) else {
            log(&format!(
                "could not get descriptor for path: {}",
                path.display()
            ));
            return Ok(None);
        };
        let Some(env) = project.get_env(&descriptor) else {
            log(&format!(
                "no environment for module: {:?} (try saving?)",
                descriptor
            ));
            return Ok(None);
        };

        Ok(project
            .definition_location(&env, pos.line, pos.character)
            .map(GotoDefinitionResponse::Scalar))
    }
}

pub async fn run_server(args: &ServerArgs) {
    // By default the stack traces contain a bunch of incomprehensible framework stuff.
    // This tries to clean it up.
    BacktracePrinter::new()
        .add_frame_filter(Box::new(|frames| {
            frames.retain(|frame| {
                let name = frame.name.as_deref().unwrap_or("");
                if name.contains("acorn::") {
                    return true;
                }
                false
            });
        }))
        .install(color_backtrace::default_output_stream());

    let stdin = tokio::io::stdin();
    let stdout = tokio::io::stdout();

    let (service, socket) = LspService::build(move |client| {
        AcornLanguageServer::new(Arc::new(client), args).expect("failed to create language server")
    })
    .custom_method(
        "acorn/progress",
        AcornLanguageServer::handle_progress_request,
    )
    .custom_method(
        "acorn/selection",
        AcornLanguageServer::handle_selection_request,
    )
    .finish();

    Server::new(stdin, stdout, socket).serve(service).await;
}
