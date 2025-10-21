// Interfaces between the language server and various consumers.
// The "Params" structs are requests that come into the language server.
// The "Response" structs are responses that go out of the language server.
//
// This file should be kept parallel to vscode/interfaces.d.ts.

use std::collections::HashMap;

use serde::{Deserialize, Serialize};
use tower_lsp::lsp_types::{Range, Url};

use crate::saturation::{Outcome, Prover};

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

// The SearchParams are sent from extension to language server to start searching for a proof.
//
// NOTE: this struct defines the format used for the params in JavaScript as well.
//  See:
//  the SearchParams interface in extension.ts
#[derive(Debug, Eq, PartialEq, Clone, Deserialize, Serialize)]
#[serde(rename_all = "camelCase")]
pub struct SearchParams {
    // Which document
    pub uri: Url,
    pub version: i32,

    // The selected line in the document
    pub selected_line: u32,

    // The search id, set by the extension.
    pub id: i32,
}

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
pub struct ClauseInfo {
    // A format for the user to see.
    // None if this is a contradiction.
    pub text: Option<String>,

    // Only activated clauses have an id
    pub id: Option<usize>,
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

// Information about one step in a proof.
#[derive(Debug, Eq, PartialEq, Clone, Deserialize, Serialize)]
#[serde(rename_all = "camelCase")]
pub struct ProofStepInfo {
    // The clause we are proving
    pub clause: ClauseInfo,

    // The clauses that we used to prove this one.
    // Each clause is tagged with its description.
    pub premises: Vec<(String, ClauseInfo)>,

    // Description of the rule used in this proof step
    pub rule: String,

    // Location is set when this proof step is based on a specific part of a codebase,
    // and we can find a location for it.
    pub location: Option<Location>,

    // The depth of this proof step in the proof tree, counting only expensive deductions.
    // TODO: should we get rid of this?
    pub depth: u32,
}

// The SearchStatus contains information about a search which may be finished, or may be in progress.
// outcome is None while the search is in progress.
#[derive(Debug, Eq, PartialEq, Clone, Deserialize, Serialize)]
#[serde(rename_all = "camelCase")]
pub struct SearchStatus {
    // Code for the proof that can be inserted.
    // This code has a standardized indentation. The base level is zero, and tabs are used for
    // nexted levels. The UI is responsible for making indentation match the surroundings.
    // If we don't have a proof, this is None.
    pub code: Option<Vec<String>>,

    // If we failed to generate the "code" field, this is the error message.
    pub code_error: Option<String>,

    // Steps in the proof, as we found them.
    // If we failed to find a proof, this is None.
    pub steps: Option<Vec<ProofStepInfo>>,

    // A stringification of the prover's Outcome, if it has finished.
    pub outcome: Option<String>,

    // Whether this proof needs simplification.
    // None if the search hasn't succeeded, so we don't have a proof.
    pub needs_simplification: Option<bool>,

    // How many clauses we have activated.
    // Any id below this, we can handle info requests to provide information for it.
    pub num_activated: usize,
}

impl SearchStatus {
    pub fn default() -> SearchStatus {
        SearchStatus {
            code: None,
            code_error: None,
            steps: None,
            outcome: None,
            needs_simplification: None,
            num_activated: 0,
        }
    }

    // Indicate that the search found a proof
    pub fn success(
        code: Option<Vec<String>>,
        code_error: Option<String>,
        steps: Vec<ProofStepInfo>,
        needs_simplification: bool,
        prover: &Prover,
    ) -> SearchStatus {
        SearchStatus {
            code,
            code_error,
            steps: Some(steps),
            outcome: Some(Outcome::Success.to_string()),
            needs_simplification: Some(needs_simplification),
            num_activated: prover.num_activated(),
        }
    }

    // Indicate that the search is still ongoing.
    pub fn pending(prover: &Prover) -> SearchStatus {
        SearchStatus {
            code: None,
            code_error: None,
            steps: None,
            outcome: None,
            needs_simplification: None,
            num_activated: prover.num_activated(),
        }
    }

    // Indicate that the search failed to find a proof, and has stopped.
    pub fn stopped(prover: &Prover, outcome: &Outcome) -> SearchStatus {
        SearchStatus {
            code: None,
            code_error: None,
            steps: None,
            outcome: Some(outcome.to_string()),
            needs_simplification: None,
            num_activated: prover.num_activated(),
        }
    }
}

// The SearchResponse is sent from language server -> extension -> webview with the result of a
// proof search, or information about a partial result.
//
// The SearchResponse will be polled until the SearchResult is available, so it can
// contain data that is updated over time.
#[derive(Debug, Eq, PartialEq, Clone, Deserialize, Serialize)]
#[serde(rename_all = "camelCase")]
pub struct SearchResponse {
    // Which document this search is for.
    pub uri: Url,
    pub version: i32,

    // A failure is distinct from an error. An error is a problem with the language server,
    // or the extension. Those are reported as jsonrpc errors.
    // A failure is when the user requested some operation that we can't do.
    // When we have a failure, this contains a failure message.
    pub failure: Option<String>,

    // When loading is true, it means that we can't start a search, because the version
    // requested is not loaded. The caller can wait and retry, or just abandon.
    pub loading: bool,

    // Information about the goal
    pub goal_name: Option<String>,
    pub goal_range: Option<Range>,

    // The line where we would insert a proof for this goal.
    // For "by" blocks, we add the keyword at the end of the line.
    // For other blocks, we insert the proof at the beginning of the line.
    pub proof_insertion_line: u32,

    // Whether we need to insert a new "by" block to hold code for this proof.
    pub insert_block: bool,

    // The status of the search process.
    pub status: SearchStatus,

    // The id for the search, provided by the extension
    pub id: i32,
}

impl SearchResponse {
    pub fn new(params: SearchParams) -> SearchResponse {
        SearchResponse {
            uri: params.uri,
            version: params.version,
            failure: None,
            loading: false,
            goal_name: None,
            goal_range: None,
            status: SearchStatus::default(),
            proof_insertion_line: 0,
            insert_block: false,
            id: params.id,
        }
    }
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

    // Information about the goal at this location, if any
    pub goal_name: Option<String>,
    pub goal_range: Option<Range>,

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
            goal_name: None,
            goal_range: None,
            id: params.id,
        }
    }
}

// The InfoParams are sent from webview -> extension -> language server, when the user is requesting
// more information about a search in progress.
//
// NOTE: keep this parallel to interfaces.ts in the webview.
#[derive(Debug, Eq, PartialEq, Clone, Deserialize, Serialize)]
#[serde(rename_all = "camelCase")]
pub struct InfoParams {
    // Each info request is associated with a single proof search.
    // We track this correlation using the id for the search request.
    pub search_id: i32,

    // Which clause we are requesting information for
    pub clause_id: usize,
}

// The InfoResult is sent from language server -> extension -> webview with the result of
// an info request.
#[derive(Debug, Eq, PartialEq, Clone, Deserialize, Serialize)]
#[serde(rename_all = "camelCase")]
pub struct InfoResult {
    // How we proved this clause
    pub step: ProofStepInfo,

    // The clauses that this clause can be used to prove.
    // Might be truncated.
    pub consequences: Vec<ProofStepInfo>,

    // The full number of consequences.
    // If this is larger than the length of consequences, we truncated the list.
    pub num_consequences: usize,
}

// If the request is out of sync with the server state, and we want to just ignore this request,
// returns a None result, along with a failure string describing what happened.
#[derive(Debug, Eq, PartialEq, Clone, Deserialize, Serialize)]
#[serde(rename_all = "camelCase")]
pub struct InfoResponse {
    // Matching to the request
    pub search_id: i32,

    pub failure: Option<String>,
    pub result: Option<InfoResult>,
}
