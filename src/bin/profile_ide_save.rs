// A representative IDE save cycle, to use for profiling language-server latency.
// This simulates opening a file, saving a tiny edit, and waiting for the
// language-server build to finish. It copies the target workspace into a
// temporary directory first, so the simulated save can exercise normal cache
// writes without modifying the real workspace.
//
// Example:
//
//   cargo run --profile fastdev --bin profile_ide_save -- acornlib/src/real/default.ac
//
// To profile using samply:
//
//   cargo build --bin=profile_ide_save --profile=fastdev
//   samply record target/fastdev/profile_ide_save acornlib/src/real/default.ac

use acorn::interfaces::ProgressParams;
use acorn::server::{AcornLanguageServer, LspClient, ServerArgs};
use mimalloc::MiMalloc;
use std::path::{Path, PathBuf};
use std::sync::Arc;
use std::time::{Duration, Instant};
use tower_lsp::lsp_types::{
    Diagnostic, DidOpenTextDocumentParams, DidSaveTextDocumentParams, TextDocumentIdentifier,
    TextDocumentItem, Url,
};
use tower_lsp::LanguageServer;
use walkdir::WalkDir;

#[global_allocator]
static GLOBAL: MiMalloc = MiMalloc;

struct NullClient;

#[async_trait::async_trait]
impl LspClient for NullClient {
    async fn publish_diagnostics(
        &self,
        _uri: Url,
        _diagnostics: Vec<Diagnostic>,
        _version: Option<i32>,
    ) {
    }
}

fn format_duration(duration: Duration) -> String {
    let seconds = duration.as_secs_f64();
    if seconds >= 1.0 {
        format!("{:.3}s", seconds)
    } else {
        format!("{:.1}ms", seconds * 1000.0)
    }
}

fn target_path() -> PathBuf {
    let arg = std::env::args()
        .nth(1)
        .unwrap_or_else(|| "acornlib/src/real/default.ac".to_string());
    let path = PathBuf::from(arg);
    if path.is_absolute() {
        path
    } else {
        std::env::current_dir().unwrap().join(path)
    }
}

fn workspace_root_for(target: &Path) -> PathBuf {
    for ancestor in target.ancestors() {
        if ancestor.join("acorn.toml").is_file() && ancestor.join("src").is_dir() {
            return ancestor.to_path_buf();
        }
    }
    panic!(
        "could not find Acorn workspace root for {}",
        target.display()
    );
}

fn copy_file(source: &Path, destination: &Path) {
    if let Some(parent) = destination.parent() {
        std::fs::create_dir_all(parent)
            .unwrap_or_else(|e| panic!("failed to create {}: {}", parent.display(), e));
    }
    std::fs::copy(source, destination).unwrap_or_else(|e| {
        panic!(
            "failed to copy {} to {}: {}",
            source.display(),
            destination.display(),
            e
        )
    });
}

fn copy_tree(source_root: &Path, destination_root: &Path) {
    for entry in WalkDir::new(source_root) {
        let entry =
            entry.unwrap_or_else(|e| panic!("failed to walk {}: {}", source_root.display(), e));
        let relative_path = entry
            .path()
            .strip_prefix(source_root)
            .expect("walked entry should be under source root");
        let destination = destination_root.join(relative_path);
        if entry.file_type().is_dir() {
            std::fs::create_dir_all(&destination)
                .unwrap_or_else(|e| panic!("failed to create {}: {}", destination.display(), e));
        } else if entry.file_type().is_file() {
            copy_file(entry.path(), &destination);
        }
    }
}

fn copy_workspace(source_root: &Path, destination_root: &Path) {
    std::fs::create_dir_all(destination_root)
        .unwrap_or_else(|e| panic!("failed to create {}: {}", destination_root.display(), e));
    copy_file(
        &source_root.join("acorn.toml"),
        &destination_root.join("acorn.toml"),
    );
    copy_tree(&source_root.join("src"), &destination_root.join("src"));
    let source_build = source_root.join("build");
    let destination_build = destination_root.join("build");
    if source_build.is_dir() {
        copy_tree(&source_build, &destination_build);
    } else {
        std::fs::create_dir_all(&destination_build)
            .unwrap_or_else(|e| panic!("failed to create {}: {}", destination_build.display(), e));
    }
}

async fn wait_for_build(server: &AcornLanguageServer) -> Duration {
    let start = Instant::now();
    loop {
        let progress = server
            .handle_progress_request(ProgressParams {})
            .await
            .expect("progress request failed");
        if progress.finished {
            return start.elapsed();
        }
        tokio::time::sleep(Duration::from_millis(10)).await;
    }
}

#[tokio::main]
async fn main() {
    let setup_start = Instant::now();
    let source_target_path = target_path();
    let source_workspace_root = workspace_root_for(&source_target_path);
    let relative_target_path = source_target_path
        .strip_prefix(&source_workspace_root)
        .unwrap_or_else(|_| {
            panic!(
                "target {} is not under workspace root {}",
                source_target_path.display(),
                source_workspace_root.display()
            )
        });
    let temp_dir = tempfile::tempdir().expect("failed to create temporary directory");
    let workspace_root = temp_dir.path().join("workspace");
    copy_workspace(&source_workspace_root, &workspace_root);
    let target_path = workspace_root.join(relative_target_path);
    let setup_time = setup_start.elapsed();

    let total_start = Instant::now();
    let original_text = std::fs::read_to_string(&target_path)
        .unwrap_or_else(|e| panic!("failed to read {}: {}", target_path.display(), e));
    let mut saved_text = original_text.clone();
    saved_text.push(' ');

    let args = ServerArgs {
        workspace_root: Some(workspace_root.to_string_lossy().into_owned()),
        acornlib_cache_dir: None,
        #[cfg(test)]
        packaged_acornlib_override: None,
    };

    let server_start = Instant::now();
    let server =
        AcornLanguageServer::new(Arc::new(NullClient), &args).expect("server creation failed");
    let server_time = server_start.elapsed();

    let uri = Url::from_file_path(&target_path)
        .unwrap_or_else(|_| panic!("failed to create file URL for {}", target_path.display()));

    let open_start = Instant::now();
    server
        .did_open(DidOpenTextDocumentParams {
            text_document: TextDocumentItem {
                uri: uri.clone(),
                language_id: "acorn".to_string(),
                version: 1,
                text: original_text,
            },
        })
        .await;
    let open_time = open_start.elapsed();

    let save_start = Instant::now();
    server
        .did_save(DidSaveTextDocumentParams {
            text_document: TextDocumentIdentifier { uri: uri.clone() },
            text: Some(saved_text),
        })
        .await;
    let save_call_time = save_start.elapsed();
    let build_wait_time = wait_for_build(&server).await;

    println!(
        "profile_ide_save source target: {}",
        source_target_path.display()
    );
    println!("scratch target: {}", target_path.display());
    println!(
        "setup copy time: {} (excluded)",
        format_duration(setup_time)
    );
    println!("workspace root: {}", workspace_root.display());
    println!("server startup: {}", format_duration(server_time));
    println!("did_open call: {}", format_duration(open_time));
    println!("did_save call: {}", format_duration(save_call_time));
    println!(
        "build wait after did_save: {}",
        format_duration(build_wait_time)
    );
    println!("total measured: {}", format_duration(total_start.elapsed()));
}
