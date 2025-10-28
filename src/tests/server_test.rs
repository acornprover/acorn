use crate::interfaces::ProgressParams;
use crate::server::{AcornLanguageServer, LspClient, ServerArgs};
use assert_fs::fixture::ChildPath;
use assert_fs::prelude::*;
use assert_fs::TempDir;
use std::collections::HashMap;
use std::sync::Arc;
use std::time::Duration;
use tokio::sync::RwLock;
use tower_lsp::lsp_types::{
    Diagnostic, DidChangeTextDocumentParams, DidOpenTextDocumentParams, DidSaveTextDocumentParams,
    TextDocumentContentChangeEvent, TextDocumentIdentifier, TextDocumentItem, Url,
    VersionedTextDocumentIdentifier,
};
use tower_lsp::LanguageServer;

/// Mock implementation of LspClient for testing
#[derive(Clone)]
struct MockClient {
    // Store diagnostics by URL
    diagnostics: Arc<RwLock<HashMap<Url, Vec<Diagnostic>>>>,
}

impl MockClient {
    fn new() -> Self {
        MockClient {
            diagnostics: Arc::new(RwLock::new(HashMap::new())),
        }
    }

    /// Wait for diagnostics to be published for a given URL
    /// Returns the diagnostics if they arrive within the timeout
    async fn wait_for_diagnostics(&self, url: &Url, timeout_secs: u64) -> Option<Vec<Diagnostic>> {
        let deadline = tokio::time::Instant::now() + Duration::from_secs(timeout_secs);

        while tokio::time::Instant::now() < deadline {
            {
                let diags = self.diagnostics.read().await;
                if let Some(diagnostics) = diags.get(url) {
                    if !diagnostics.is_empty() || diags.contains_key(url) {
                        // Return if we have diagnostics or an explicit empty list
                        return Some(diagnostics.clone());
                    }
                }
            }
            // Check every 10ms
            tokio::time::sleep(Duration::from_millis(10)).await;
        }
        None
    }
}

#[async_trait::async_trait]
impl LspClient for MockClient {
    async fn publish_diagnostics(
        &self,
        uri: Url,
        diagnostics: Vec<Diagnostic>,
        _version: Option<i32>,
    ) {
        let mut diags = self.diagnostics.write().await;
        diags.insert(uri, diagnostics);
    }
}

/// Test fixture that sets up an Acorn language server with a temp directory.
/// Automatically cleans up when dropped.
struct TestFixture {
    _temp_dir: TempDir, // Must keep this alive or the directory gets deleted!
    pub src_dir: ChildPath,
    pub build_dir: ChildPath,
    pub client: Arc<MockClient>,
    pub server: AcornLanguageServer,
}

impl TestFixture {
    /// Creates a new test fixture with standard Acorn project layout
    fn new() -> Self {
        // Create temp directory structure
        let temp_dir = TempDir::new().unwrap();
        temp_dir.child("acorn.toml").write_str("").unwrap();
        let src_dir = temp_dir.child("src");
        src_dir.create_dir_all().unwrap();
        let build_dir = temp_dir.child("build");
        build_dir.create_dir_all().unwrap();

        // This is the "developing acornlib" setup
        let args = ServerArgs {
            workspace_root: Some(temp_dir.path().to_str().unwrap().to_string()),
            extension_root: String::new(),
        };

        let client = Arc::new(MockClient::new());
        let server = AcornLanguageServer::new(client.clone(), &args);

        TestFixture {
            _temp_dir: temp_dir,
            src_dir,
            build_dir,
            client,
            server,
        }
    }

    /// Converts a relative path to a file:// URL
    fn url(&self, path: &str) -> Url {
        let full_path = self.src_dir.path().join(path);
        Url::from_file_path(full_path).unwrap()
    }

    /// Open a document with the given content
    async fn open(&self, filename: &str, content: &str, version: i32) {
        self.server
            .did_open(DidOpenTextDocumentParams {
                text_document: TextDocumentItem {
                    uri: self.url(filename),
                    language_id: "acorn".to_string(),
                    version,
                    text: content.to_string(),
                },
            })
            .await;
    }

    /// Change a document's content (replaces entire content)
    async fn change(&self, filename: &str, content: &str, version: i32) {
        self.server
            .did_change(DidChangeTextDocumentParams {
                text_document: VersionedTextDocumentIdentifier {
                    uri: self.url(filename),
                    version,
                },
                content_changes: vec![TextDocumentContentChangeEvent {
                    range: None,
                    range_length: None,
                    text: content.to_string(),
                }],
            })
            .await;
    }

    /// Save a document with the given content
    async fn save(&self, filename: &str, content: &str) {
        self.server
            .did_save(DidSaveTextDocumentParams {
                text_document: TextDocumentIdentifier {
                    uri: self.url(filename),
                },
                text: Some(content.to_string()),
            })
            .await;
    }

    /// Assert that the current build completes within 5 seconds
    async fn assert_build_completes(&self) {
        let deadline = tokio::time::Instant::now() + Duration::from_secs(5);

        while tokio::time::Instant::now() < deadline {
            let progress = self
                .server
                .handle_progress_request(ProgressParams {})
                .await
                .unwrap();

            if progress.finished {
                return;
            }

            // Poll every 10ms
            tokio::time::sleep(Duration::from_millis(10)).await;
        }

        panic!("Build did not complete within 5 seconds");
    }

    /// Assert that a file in the build directory will exist within 5 seconds
    async fn assert_build_file_will_exist(&self, filename: &str) {
        let deadline = tokio::time::Instant::now() + Duration::from_secs(5);
        let path = self.build_dir.child(filename);

        while tokio::time::Instant::now() < deadline {
            if path.exists() {
                return;
            }
            // Poll every 10ms
            tokio::time::sleep(Duration::from_millis(10)).await;
        }

        panic!("Build file did not exist within 5 seconds: {}", filename);
    }
}

#[tokio::test(flavor = "multi_thread")]
async fn test_non_library_file_certificates() {
    let fx = TestFixture::new();

    // Create a file outside the src directory (simulating a file outside the library)
    let outside_dir = fx._temp_dir.child("outside");
    outside_dir.create_dir_all().unwrap();
    let outside_file = outside_dir.child("external.ac");
    let outside_path = outside_file.path();
    let outside_url = Url::from_file_path(outside_path).unwrap();

    // Write initial content
    let content = r#"
    let external_thing: Bool = axiom
    theorem external_theorem {
        external_thing = external_thing
    }
    "#;
    outside_file.write_str(content).unwrap();

    // Open the file in the language server
    fx.server
        .did_open(DidOpenTextDocumentParams {
            text_document: TextDocumentItem {
                uri: outside_url.clone(),
                language_id: "acorn".to_string(),
                version: 1,
                text: content.to_string(),
            },
        })
        .await;

    // Save the file to trigger a build (opens no longer trigger builds)
    fx.server
        .did_save(DidSaveTextDocumentParams {
            text_document: TextDocumentIdentifier {
                uri: outside_url.clone(),
            },
            text: Some(content.to_string()),
        })
        .await;

    // Wait for the build to complete
    fx.assert_build_completes().await;

    // Give it a bit more time for file I/O
    tokio::time::sleep(Duration::from_millis(100)).await;

    // Check that a JSONL file was created alongside the .ac file
    let jsonl_file = outside_dir.child("external.jsonl");
    assert!(
        jsonl_file.exists(),
        "JSONL file should be created alongside the .ac file for non-library files"
    );

    // Verify the JSONL file contains certificate data
    let jsonl_content = std::fs::read_to_string(jsonl_file.path()).unwrap();
    assert!(
        jsonl_content.contains("external_theorem"),
        "JSONL file should contain certificate for external_theorem"
    );

    // Verify that the manifest in the build directory does NOT contain this file
    let manifest_file = fx.build_dir.child("manifest.json");
    if manifest_file.exists() {
        let manifest_content = std::fs::read_to_string(manifest_file.path()).unwrap();
        assert!(
            !manifest_content.contains("external"),
            "Manifest should not contain entries for files outside the library"
        );
    }
}

#[tokio::test(flavor = "multi_thread")]
async fn test_server_basic() {
    let fx = TestFixture::new();

    let text1 = "theorem foo { true }";
    let text2 = "theorem bar { true }";

    fx.open("foo.ac", text1, 1).await;
    fx.change("foo.ac", text2, 2).await;
    fx.save("foo.ac", text2).await;

    // Wait for diagnostics to verify the build happened
    let url = fx.url("foo.ac");
    let diagnostics = fx.client.wait_for_diagnostics(&url, 5).await;
    assert!(
        diagnostics.is_some(),
        "Expected to receive diagnostics from build"
    );

    // The build should complete with no errors for this simple valid theorem
    let diags = diagnostics.unwrap();
    assert!(
        diags.is_empty(),
        "Expected no diagnostic errors, got: {:?}",
        diags
    );
    fx.assert_build_completes().await;

    // Check that certificates were created
    fx.assert_build_file_will_exist("foo.jsonl").await;
}

#[tokio::test(flavor = "multi_thread")]
async fn test_build_cancellation() {
    let fx = TestFixture::new();

    // Start with a theorem that will hang forever (in test mode)
    let hanging_text = "theorem test_hang { true }";
    fx.open("test.ac", hanging_text, 1).await;
    fx.save("test.ac", hanging_text).await;

    // Give the build a moment to start
    tokio::time::sleep(Duration::from_millis(50)).await;

    // Now change the file to have a normal theorem
    // This should cancel the hanging build and start a new one
    let normal_text = "theorem foo { true }";
    fx.change("test.ac", normal_text, 2).await;
    fx.save("test.ac", normal_text).await;

    // The new build should complete successfully
    fx.assert_build_completes().await;

    // Check that certificates were created for the successful build
    fx.assert_build_file_will_exist("test.jsonl").await;
}

#[tokio::test(flavor = "multi_thread")]
async fn test_selection_after_fresh_build() {
    use crate::interfaces::SelectionParams;
    use indoc::indoc;

    let fx = TestFixture::new();

    // Create a file with a simple theorem
    let content = indoc! {"
        type Nat: axiom
        let f: Nat -> Bool = axiom
        let g: Nat -> Bool = axiom
        let h: Nat -> Bool = axiom

        axiom a1(x: Nat) {
            f(x) implies g(x)
        }

        axiom a2(x: Nat) {
            g(x) implies h(x)
        }

        theorem simple_theorem(x: Nat) {
            f(x) implies h(x)
        }
    "};
    fx.open("test.ac", content, 1).await;
    fx.save("test.ac", content).await;

    // Wait for the build to complete and certificates to be created
    fx.assert_build_completes().await;
    fx.assert_build_file_will_exist("test.jsonl").await;

    // Give a bit more time for the build cache to be updated
    tokio::time::sleep(Duration::from_millis(100)).await;

    // Now request selection information for the theorem line
    let url = fx.url("test.ac");
    let params = SelectionParams {
        uri: url,
        version: 1,
        selected_line: 14, // The theorem is on line 14
        id: 1,
    };

    let response = fx.server.handle_selection_request(params).await.unwrap();

    // Verify the goal was found
    assert_eq!(response.goal_name, Some("simple_theorem".to_string()));
    assert!(response.goal_range.is_some());

    // Even for trivial proofs, we should get Some([]) rather than None
    assert!(
        response.steps.is_some(),
        "Expected steps to be returned from cached proof (got None)."
    );
}

#[tokio::test(flavor = "multi_thread")]
async fn test_selection_inside_partially_complete_proof() {
    use crate::interfaces::SelectionParams;
    use indoc::indoc;

    let fx = TestFixture::new();

    // Create a file with a theorem that has a proof block
    let content = indoc! {"
        type Nat: axiom

        theorem foo(a: Nat, b: Nat) {
            a = b
        } by {
            a = a
        }
    "};
    fx.open("test.ac", content, 1).await;
    fx.save("test.ac", content).await;

    // Wait for the build to complete
    // Note: The overall theorem won't verify, but individual statements inside should have certificates
    fx.assert_build_completes().await;

    // Give a bit more time for the build cache to be updated
    tokio::time::sleep(Duration::from_millis(100)).await;

    // Now request selection information for the statement inside the proof block
    // Line 5 is "a = a" which should have a certificate even though the overall theorem doesn't verify
    let url = fx.url("test.ac");
    let params = SelectionParams {
        uri: url,
        version: 1,
        selected_line: 5,
        id: 1,
    };

    let response = fx.server.handle_selection_request(params).await.unwrap();

    // We should get the proof steps for "a = a" statement inside proof block
    assert!(
        response.steps.is_some(),
        "Expected steps to be returned for 'a = a' statement inside proof block (got None). Goal name: {:?}",
        response.goal_name
    );
}
