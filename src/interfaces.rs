// Interfaces between the language server and various consumers.
// The "Params" structs are requests that come into the language server.
// The "Response" structs are responses that go out of the language server.
//
// This file should be kept parallel to vscode/interfaces.d.ts.

use std::collections::HashMap;

use serde::{Deserialize, Serialize};
use tower_lsp::lsp_types::{Range, Url};

// Verification progress for a single document.
#[derive(Debug, Eq, PartialEq, Clone, Deserialize, Serialize)]
#[serde(rename_all = "camelCase")]
pub struct DocumentProgress {
    // We only report document progress for versioned documents.
    pub version: i32,

    // Line ranges that have been verified.
    pub verified: Vec<(u32, u32)>,
}

// The ProgressResponse reports the progress for a build overall.
#[derive(Debug, Eq, PartialEq, Clone, Deserialize, Serialize)]
#[serde(rename_all = "camelCase")]
pub struct ProgressResponse {
    // Which build we are tracking progress for, if any.
    pub build_id: Option<u32>,

    // How many goals the build has gotten through.
    pub done: i32,
    pub total: i32,

    // Whether this build has finished.
    pub finished: bool,

    // Per-document progress information.
    pub docs: HashMap<Url, DocumentProgress>,
}

impl ProgressResponse {
    pub fn default() -> ProgressResponse {
        ProgressResponse {
            build_id: None,
            done: 0,
            total: 0,
            finished: false,
            docs: HashMap::new(),
        }
    }
}

#[derive(Debug, Eq, PartialEq, Clone, Deserialize, Serialize)]
#[serde(rename_all = "camelCase")]
pub struct ProgressParams {}

#[derive(Debug, Eq, PartialEq, Clone, Deserialize, Serialize)]
#[serde(rename_all = "camelCase")]
pub struct SelectionParams {
    // Which document
    pub uri: Url,
    pub version: i32,

    // The selected line in the document
    pub selected_line: u32,

    // The selection id, set by the extension.
    pub id: u32,
}

#[derive(Debug, Eq, PartialEq, Clone, Deserialize, Serialize)]
#[serde(rename_all = "camelCase")]
pub struct Location {
    // Which document this assumption was made in.
    pub uri: Url,

    // The range in the source document corresponding to this proposition.
    // This is here for UI purposes. It is the place we should jump to or highlight to show
    // the user where this proposition is defined.
    pub range: Range,
}

// Information about one step in a cached proof.
#[derive(Debug, Eq, PartialEq, Clone, Deserialize, Serialize)]
#[serde(rename_all = "camelCase")]
pub struct Step {
    // The statement from the certificate (a normalized line of code).
    pub statement: String,

    // The reason this step is valid.
    pub reason: String,

    // Location is set when this step is based on a specific part of the codebase.
    pub location: Option<Location>,
}

// Information about a single goal.
#[derive(Debug, Eq, PartialEq, Clone, Deserialize, Serialize)]
#[serde(rename_all = "camelCase")]
pub struct GoalInfo {
    pub goal_name: String,

    // Whether there is a cached proof that verifies for this goal
    pub has_cached_proof: bool,

    // The steps from the cached proof, if the goal has a proof
    pub steps: Option<Vec<Step>>,
}

#[derive(Debug, Eq, PartialEq, Clone, Deserialize, Serialize)]
#[serde(rename_all = "camelCase")]
pub struct CitationInfo {
    // The selected citation statement, shown in the header.
    pub selection_text: String,

    // The range of the selected citation in the source document.
    pub range: Range,

    // The cited theorem name, if available.
    pub theorem_name: Option<String>,

    // The definition location of the cited theorem, if available.
    pub theorem_location: Option<Location>,

    // The lowered-and-quoted normalized expansion of the citation.
    pub expansion: String,
}

// The SelectionResponse is sent from language server -> extension with information about what
// is at the selected line, without starting a proof search.
#[derive(Debug, Eq, PartialEq, Clone, Deserialize, Serialize)]
#[serde(rename_all = "camelCase")]
pub struct SelectionResponse {
    // Which document this selection is for.
    pub uri: Url,
    pub version: i32,

    // A failure is when the user requested some operation that we can't do.
    // When we have a failure, this contains a failure message.
    pub failure: Option<String>,

    // When loading is true, it means that we can't process this selection, because the version
    // requested is not loaded. The caller can wait and retry, or just abandon.
    pub loading: bool,

    // When building is true, it means that a build is currently in progress.
    pub building: bool,

    // The range of the goal(s) at this location. This is the same for all goals.
    pub goal_range: Option<Range>,

    // Information about all goals at this location
    pub goals: Vec<GoalInfo>,

    // Citation information when the selected line is a direct theorem citation.
    pub citation: Option<CitationInfo>,

    // The id for the selection, provided by the extension
    pub id: u32,
}

impl SelectionResponse {
    pub fn new(params: SelectionParams) -> SelectionResponse {
        SelectionResponse {
            uri: params.uri,
            version: params.version,
            failure: None,
            loading: false,
            building: false,
            goal_range: None,
            goals: vec![],
            citation: None,
            id: params.id,
        }
    }
}
